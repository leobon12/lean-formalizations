import HigherDimLQGMetric.Bilip.ShellGeometry
import HigherDimLQGMetric.ShellDec.Bridge

/-!
# Metric shell decoupling

The metric analogue of the Gaussian shell count estimate, using joint
ξ-additive locality and Borel chain representatives of internal metrics.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open LQGMetric
open LQGMetric.GM.Bilip
open HigherDimLFPP (Rd)
open scoped ENNReal

namespace HigherDimLQGMetric

variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]

private lemma bilip_aeClosure_trans {P : Measure[mΩ] Ω}
    {A B C : MeasurableSpace Ω}
    (hAB : A ≤ aeClosure P B) (hBC : B ≤ aeClosure P C) :
    A ≤ aeClosure P C :=
  hAB.trans ((aeClosure_mono hBC).trans (aeClosure_aeClosure_le C))

/-- The field restricted to an annulus after recentering is an observation of
the original full field. -/
theorem bilip_shellField_le_full (h : Ω → DistRd d) (z : Rd d) (r a b : ℝ) :
    fieldSigmaRd (fun ω => l7b_recenter (h ω) r z)
        (shellOpen z (a * r) (b * r)) ≤ fullSigmaRd h := by
  have hres : fieldSigmaRd (fun ω => l7b_recenter (h ω) r z)
      (shellOpen z (a * r) (b * r)) ≤
        fullSigmaRd (fun ω => l7b_recenter (h ω) r z) :=
    ((measurable_restrictTo (shellOpen z (a * r) (b * r))).comp
      (comap_measurable (fun ω => l7b_recenter (h ω) r z))).comap_le
  exact hres.trans (l7b_recenterSigma_le_fullSigma h r z)

/-- The rational-chain observation is measurable whenever the field and metric
are measurable. -/
theorem bilip_shellChainSigma_le_ambient
    (ξ : ℝ) {h : Ω → DistRd d} {D : Ω → ContMetric d}
    (hh : Measurable[mΩ] h) (hD : Measurable[mΩ] D)
    (r : ℝ) (z : Rd d) (V : Set (Rd d)) :
    famSigmaRd (l7b_chainFam ξ h D r z) V ≤ mΩ := by
  exact (l7b_measurable_chainFam ξ hh hD r z V).comap_le

/-- The field and chain representatives on separated shells satisfy the exact
conditional-independence hypotheses needed for finite product probabilities. -/
private theorem bilip_shell_local_setup (hd : 2 ≤ d) {ξ : ℝ}
    {P : Measure[mΩ] Ω} [IsProbabilityMeasure P]
    {h : Ω → DistRd d} {D₁ D₂ : Ω → ContMetric d}
    (hh : IsNormalizedLGF h P) (hxi : IsXiAdditiveRd ξ P h D₁ D₂)
    {a b q : ℝ} (ha1 : a < 1) (hb : 1 < b) (hq : 0 < q)
    (hgap : b * q < a) (z : Rd d) (r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i) (hstep : ∀ i, r (i + 1) ≤ q * r i) :
    let V : ℕ → TopologicalSpace.Opens (Rd d) :=
      fun i => shellOpen z (a * r i) (b * r i)
    let W : ℕ → Set (Rd d) :=
      fun i => (closure (V i : Set (Rd d)))ᶜ
    let H : MeasurableSpace Ω := fullSigmaRd h
    let G : ℕ → MeasurableSpace Ω := fun i =>
      fieldSigmaRd (fun ω => l7b_recenter (h ω) (r i) z) (V i)
    let A : ℕ → MeasurableSpace Ω := fun i =>
      famSigmaRd (l7b_chainFam ξ h D₁ (r i) z) (V i) ⊔
      famSigmaRd (l7b_chainFam ξ h D₂ (r i) z) (V i)
    let B : ℕ → MeasurableSpace Ω := fun i =>
      famSigmaRd (l7b_chainFam ξ h D₁ (r i) z) (W i) ⊔
      famSigmaRd (l7b_chainFam ξ h D₂ (r i) z) (W i)
    (∀ i, G i ≤ H) ∧ (H ≤ mΩ) ∧ (∀ i, A i ≤ mΩ) ∧
      (∀ i, B i ≤ mΩ) ∧
      (∀ i, CondIndepEv (G i) (A i) (H ⊔ B i) P) ∧
      (∀ i j, i ≠ j → A j ≤ aeClosure P (H ⊔ B i)) := by
  classical
  dsimp only
  let V : ℕ → TopologicalSpace.Opens (Rd d) :=
    fun i => shellOpen z (a * r i) (b * r i)
  let W : ℕ → Set (Rd d) := fun i => (closure (V i : Set (Rd d)))ᶜ
  let H : MeasurableSpace Ω := fullSigmaRd h
  let G : ℕ → MeasurableSpace Ω := fun i =>
    fieldSigmaRd (fun ω => l7b_recenter (h ω) (r i) z) (V i)
  let A : ℕ → MeasurableSpace Ω := fun i =>
    famSigmaRd (l7b_chainFam ξ h D₁ (r i) z) (V i) ⊔
    famSigmaRd (l7b_chainFam ξ h D₂ (r i) z) (V i)
  let B : ℕ → MeasurableSpace Ω := fun i =>
    famSigmaRd (l7b_chainFam ξ h D₁ (r i) z) (W i) ⊔
    famSigmaRd (l7b_chainFam ξ h D₂ (r i) z) (W i)
  letI : MeasurableSpace Ω := mΩ
  have hD₁ := hxi.1
  have hD₂ := hxi.2.1
  have hlen₁ : ∀ᵐ ω ∂P, (D₁ ω).IsLength := hxi.2.2.1.mono fun ω hω => hω.1
  have hlen₂ : ∀ᵐ ω ∂P, (D₂ ω).IsLength := hxi.2.2.1.mono fun ω hω => hω.2
  have hH : H ≤ mΩ := hh.1.measurable.comap_le
  have hG : ∀ i, G i ≤ H := fun i => bilip_shellField_le_full h z (r i) a b
  have hA : ∀ i, A i ≤ mΩ := by
    intro i
    exact sup_le (bilip_shellChainSigma_le_ambient ξ hh.1.measurable hD₁ (r i) z (V i))
      (bilip_shellChainSigma_le_ambient ξ hh.1.measurable hD₂ (r i) z (V i))
  have hB : ∀ i, B i ≤ mΩ := by
    intro i
    exact sup_le (bilip_shellChainSigma_le_ambient ξ hh.1.measurable hD₁ (r i) z (W i))
      (bilip_shellChainSigma_le_ambient ξ hh.1.measurable hD₂ (r i) z (W i))
  refine ⟨hG, hH, hA, hB, ?_, ?_⟩
  · intro i
    have hraw := hxi.2.2.2 z (r i) (hr i) (V i)
      (bilip_shellNice hd z (a * r i) (b * r i))
    have hAi : A i ≤ aeClosure P
        (famSigmaRd (rescFam ξ h D₁ z (r i)) (V i) ⊔
          famSigmaRd (rescFam ξ h D₂ z (r i)) (V i)) := by
      exact sup_le
        ((l7b_chainSigma_le_ae_int hlen₁ (r i) z (V i).isOpen).trans
          (aeClosure_mono le_sup_left))
        ((l7b_chainSigma_le_ae_int hlen₂ (r i) z (V i).isOpen).trans
          (aeClosure_mono le_sup_right))
    have hBi : H ⊔ B i ≤ aeClosure P
        (fullSigmaRd (fun ω => l7b_recenter (h ω) (r i) z) ⊔
          famSigmaRd (rescFam ξ h D₁ z (r i)) (W i) ⊔
          famSigmaRd (rescFam ξ h D₂ z (r i)) (W i)) := by
      apply sup_le
      · exact (l7b_fullSigma_le_aeClosure_recenter hd hh (hr i) z).trans
          (aeClosure_mono (le_sup_of_le_left le_sup_left))
      · apply sup_le
        · exact (l7b_chainSigma_le_ae_int hlen₁ (r i) z isClosed_closure.isOpen_compl).trans
            (aeClosure_mono (le_sup_of_le_left le_sup_right))
        · exact (l7b_chainSigma_le_ae_int hlen₂ (r i) z isClosed_closure.isOpen_compl).trans
            (aeClosure_mono le_sup_right)
    exact LQGMetric.GM.Bilip.CondIndepEv.of_le_aeClosure hraw hAi hBi
  · intro i j hij
    have hsub : (V j : Set (Rd d)) ⊆ W i :=
      bilip_shell_pairwise_outside_closure z ha1 hb hq hgap r hr hstep i j hij
    apply sup_le
    · have h1 := l7b_chainSigma_le_ae_int (ξ := ξ) (h := h) hlen₁ (r j) z (V j).isOpen
      have h2 := BilipNest.rescFamSigma_le_full_join (h := h) hlen₁ ξ z (r j) (r i)
        (V j).isOpen isClosed_closure.isOpen_compl hsub
      have h3 := sup_le ((le_sup_left : H ≤ H ⊔ B i).trans (le_aeClosure (H ⊔ B i)))
        ((l7b_intSigma_le_ae_chain hlen₁ (r i) z isClosed_closure.isOpen_compl).trans
          (aeClosure_mono (le_sup_of_le_right le_sup_left)))
      exact bilip_aeClosure_trans h1 (bilip_aeClosure_trans h2 h3)
    · have h1 := l7b_chainSigma_le_ae_int (ξ := ξ) (h := h) hlen₂ (r j) z (V j).isOpen
      have h2 := BilipNest.rescFamSigma_le_full_join (h := h) hlen₂ ξ z (r j) (r i)
        (V j).isOpen isClosed_closure.isOpen_compl hsub
      have h3 := sup_le ((le_sup_left : H ≤ H ⊔ B i).trans (le_aeClosure (H ⊔ B i)))
        ((l7b_intSigma_le_ae_chain hlen₂ (r i) z isClosed_closure.isOpen_compl).trans
          (aeClosure_mono (le_sup_of_le_right le_sup_right)))
      exact bilip_aeClosure_trans h1 (bilip_aeClosure_trans h2 h3)

/-- MA5 A17, the metric-shell high-probability count estimate. -/
theorem l7c_metricShell : L7c_metricShell := by
  classical
  intro d hd a b q ha ha1 hb hq hgap A₀ θ hA₀ hθ hθ1
  have hq1 : q < 1 := by
    calc q = 1 * q := (one_mul q).symm
      _ < b * q := mul_lt_mul_of_pos_right hb hq
      _ < a := hgap
      _ < 1 := ha1
  obtain ⟨K, hK, hdec⟩ := shellDecouplingFun_rd d hd a b q ha ha1 hb hq hq1
  let t : ℝ := (A₀ + 1) / (1 - θ)
  have ht : 0 < t := by dsimp [t]; positivity
  have htc : t * (1 - θ) = A₀ + 1 := by
    dsimp [t]
    have hne : 1 - θ ≠ 0 := by linarith
    field_simp
  let p : ℝ := 1 - Real.exp (-K * t)
  have hp0 : 0 ≤ p := by
    dsimp [p]
    have hneg : -K * t < 0 := by nlinarith
    have := Real.exp_lt_one_iff.mpr hneg
    linarith
  have hp1 : p < 1 := by dsimp [p]; have := Real.exp_pos (-K * t); linarith
  refine ⟨p, hp1, ?_⟩
  intro ξ Ω mΩ P hProb h D₁ D₂ hh hxi z r hr hstep E hE hprob n
  let V : ℕ → TopologicalSpace.Opens (Rd d) :=
    fun i => shellOpen z (a * r i) (b * r i)
  let W : ℕ → Set (Rd d) := fun i => (closure (V i : Set (Rd d)))ᶜ
  let H : MeasurableSpace Ω := fullSigmaRd h
  let G : ℕ → MeasurableSpace Ω := fun i =>
    fieldSigmaRd (fun ω => l7b_recenter (h ω) (r i) z) (V i)
  let A : ℕ → MeasurableSpace Ω := fun i =>
    famSigmaRd (l7b_chainFam ξ h D₁ (r i) z) (V i) ⊔
    famSigmaRd (l7b_chainFam ξ h D₂ (r i) z) (V i)
  let B : ℕ → MeasurableSpace Ω := fun i =>
    famSigmaRd (l7b_chainFam ξ h D₁ (r i) z) (W i) ⊔
    famSigmaRd (l7b_chainFam ξ h D₂ (r i) z) (W i)
  letI : MeasurableSpace Ω := mΩ
  obtain ⟨hG, hH, hA, hB, hCI, hNest⟩ :=
    bilip_shell_local_setup hd hh hxi ha1 hb hq hgap z r hr hstep
  have hlen₁ : ∀ᵐ ω ∂P, (D₁ ω).IsLength := hxi.2.2.1.mono fun ω hω => hω.1
  have hlen₂ : ∀ᵐ ω ∂P, (D₂ ω).IsLength := hxi.2.2.1.mono fun ω hω => hω.2
  have hex (i : ℕ) : ∃ E' : Set Ω,
      MeasurableSet[G i ⊔ A i] E' ∧ E i =ᵐ[P] E' := by
    have hraw₁ : famSigmaRd (rescFam ξ h D₁ z (r i)) (V i) ≤
        aeClosure P (G i ⊔ A i) :=
      (l7b_intSigma_le_ae_chain hlen₁ (r i) z (V i).isOpen).trans
        (aeClosure_mono (le_sup_of_le_right le_sup_left))
    have hraw₂ : famSigmaRd (rescFam ξ h D₂ z (r i)) (V i) ≤
        aeClosure P (G i ⊔ A i) :=
      (l7b_intSigma_le_ae_chain hlen₂ (r i) z (V i).isOpen).trans
        (aeClosure_mono (le_sup_of_le_right le_sup_right))
    have hraw : G i ⊔ famSigmaRd (rescFam ξ h D₁ z (r i)) (V i) ⊔
        famSigmaRd (rescFam ξ h D₂ z (r i)) (V i) ≤
        aeClosure P (G i ⊔ A i) :=
      sup_le (sup_le ((le_sup_left : G i ≤ G i ⊔ A i).trans
        (le_aeClosure (G i ⊔ A i))) hraw₁) hraw₂
    exact hraw _ (hE i)
  choose Good hGood hEq using hex
  have hGoodAmb (i : ℕ) : MeasurableSet[mΩ] (Good i) :=
    (sup_le ((hG i).trans hH) (hA i)) _ (hGood i)
  let Fail : ℕ → Set Ω := fun i => (Good i)ᶜ
  have hFail (i : ℕ) : MeasurableSet[G i ⊔ A i] (Fail i) := (hGood i).compl
  have hFailProb (i : ℕ) : P.real (Fail i) ≤ Real.exp (-K * t) := by
    have hprobGood : ENNReal.ofReal p ≤ P (Good i) := by
      rw [← measure_congr (hEq i)]
      exact hprob i
    have hprobR : p ≤ P.real (Good i) := by
      have h := ENNReal.toReal_mono (measure_ne_top P _) hprobGood
      simpa only [ENNReal.toReal_ofReal hp0, Measure.real] using h
    rw [probReal_compl_eq_one_sub (hGoodAmb i)]
    dsimp [p] at hprobR
    linarith
  let F : ℕ → Ω → ℝ := fun i => BilipProb.clipCondProb P (G i) (Fail i)
  have hFm (i : ℕ) : Measurable[G i] (F i) :=
    BilipProb.measurable_clipCondProb (mΩ := mΩ) P (G i) (Fail i)
  have hF01 (i : ℕ) (ω : Ω) : 0 ≤ F i ω ∧ F i ω ≤ 1 :=
    BilipProb.clipCondProb_mem_Icc (mΩ := mΩ) P (G i) (Fail i) ω
  have hsub (I : Finset ℕ) :
      P.real {ω | ∀ i ∈ I, ω ∉ Good i} ≤ Real.exp (-t * I.card) := by
    have hbi : (⋂ i ∈ I, Fail i) = {ω | ∀ i ∈ I, ω ∉ Good i} := by
      ext ω
      simp [Fail]
    rw [← hbi]
    exact BilipProb.local_failureIntersection (mΩ := mΩ) P H hH G A B hG hA hB
      hCI hNest Fail hFail K t hK hFailProb
      (fun J => hdec P h hh.1 z r hr hstep J F hFm hF01) I
  have htail := BilipProb.bilipUnionTail P Good A₀ θ t ht htc hsub n
  have hBadAE :
      {ω | (((Finset.range n).filter (fun i => ω ∈ E i)).card : ℝ) < θ * n} =ᵐ[P]
        {ω | (((Finset.range n).filter (fun i => ω ∈ Good i)).card : ℝ) < θ * n} := by
    filter_upwards [ae_all_iff.2 hEq] with ω hω
    have heq : (Finset.range n).filter (fun i => ω ∈ E i) =
        (Finset.range n).filter (fun i => ω ∈ Good i) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      exact and_congr_right fun _ => Iff.of_eq (hω i)
    simp only [heq]
  calc
    P {ω | (((Finset.range n).filter (fun i => ω ∈ E i)).card : ℝ) < θ * n} =
        P {ω | (((Finset.range n).filter (fun i => ω ∈ Good i)).card : ℝ) < θ * n} :=
      measure_congr hBadAE
    _ ≤ ENNReal.ofReal (Real.exp (-A₀ * n)) := htail

end HigherDimLQGMetric
