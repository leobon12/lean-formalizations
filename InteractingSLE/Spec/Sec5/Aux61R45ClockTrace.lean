/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvXExit

/-! # Trace reconstruction without an original finite force word -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Sec5.Aux61R45
open Restart

/-- The actual driver and closed available trace. There is no assumption about
its drift, harmonic mean or finite-word SLE law. Empty auxiliary coordinates
make the natural history depend only on the killed driver and its lifetime. -/
structure ClockSource (S : Type u) [MeasurableSpace S] where
  P : Measure S
  prob : IsProbabilityMeasure P
  y : ℝ
  U : S → ℝ≥0∞
  W₀ : ℝ≥0 → S → ℝ
  Γ : S → ℝ≥0 → ℂ
  killed : IsMeasurableKilledDriving W₀ (fun (_ : Fin 0) _ _ => 0)
    (fun (_ : Fin 0) _ _ => 0) U
  regular : ∀ᵐ ω ∂P, ContinuousOn (W₀ · ω) {t | (t : ℝ≥0∞) < U ω} ∧ W₀ 0 ω = 0
  trace : ∀ᵐ ω ∂P, IsGeneratingTrace (W₀ · ω) (U ω) (fun t => Γ ω t - y)

namespace ClockSource
variable {S : Type u} [MeasurableSpace S] (D : ClockSource S)

/-- Completed right-continuous history of the actual killed driver. -/
def driving := drivingFiltration D.P D.killed

instance driving_rightContinuous : D.driving.IsRightContinuous := by
  unfold driving drivingFiltration
  infer_instance

/-- The actual driver is adapted before its lifetime in its own history. -/
theorem adaptedBefore : AdaptedBefore D.driving D.U D.W₀ :=
  Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _)
    (Coupling.adaptedBefore_killedDriving_W D.killed)

/-- Reconstruct and regularize the closed available trace. The extension after
its lifetime is constant, and the ambient measurable space is unchanged. -/
theorem exists_continuous_measurable_trace :
    ∃ η : S → ℝ≥0 → ℂ, (∀ t, Measurable fun ω => η ω t) ∧ (∀ ω, Continuous (η ω)) ∧
      ∀ᵐ ω ∂D.P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ D.U ω → η ω t = D.Γ ω t := by
  classical
  let wk : S → ℝ≥0 → ℝ := fun ω t => if (t : ℝ≥0∞) < D.U ω then D.W₀ t ω else 0
  have hwk : Measurable wk := measurable_pi_iff.2 fun t =>
    Restart.measurable_ite_of_adaptedBefore D.adaptedBefore t
  have hUm : Measurable D.U := FlowStopIdentLift.measurable_lifetime D.killed
  let η₀ : S → ℝ≥0 → ℂ := fun ω t => (D.y : ℂ) + (LP.drivingTrace (D.U ω, wk ω)).2 t
  have hm : ∀ t, Measurable fun ω => η₀ ω t := fun t => measurable_const.add
    ((measurable_pi_apply t).comp (measurable_snd.comp
      (LP.measurable_drivingTrace.comp (hUm.prodMk hwk))))
  have hgood : ∀ᵐ ω ∂D.P, Continuous (η₀ ω) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ D.U ω → η₀ ω t = D.Γ ω t := by
    filter_upwards [D.trace, D.regular] with ω hg hp
    have hr := LP.drivingTrace_eq hg hp.1 hp.2
      (w' := wk ω) (fun s hs => ite_eq_left hs)
    have heq : ∀ t, η₀ ω t = D.Γ ω (min (t : ℝ≥0∞) (D.U ω)).toNNReal := by
      intro t
      change (D.y : ℂ) + (LP.drivingTrace (D.U ω, wk ω)).2 t = _
      rw [hr]
      dsimp only
      exact add_sub_cancel _ _
    refine ⟨?_, fun t ht => by rw [heq, min_eq_left ht, ENNReal.toNNReal_coe]⟩
    by_cases htop : D.U ω = ⊤
    · have he : η₀ ω = D.Γ ω := funext fun t => by
        rw [heq, htop, min_top_right, ENNReal.toNNReal_coe]
      rw [he]
      have hc := hg.2.1.add (continuousOn_const (c := (D.y : ℂ)))
      have hc' : ContinuousOn (D.Γ ω) Set.univ :=
        (hc.mono (fun t _ => by simp [htop])).congr (fun t _ => by
          change D.Γ ω t = D.Γ ω t - (D.y : ℂ) + D.y
          exact (sub_add_cancel _ _).symm)
      exact continuousOn_univ.1 hc'
    · let T : ℝ≥0 := (D.U ω).toNNReal
      have hT : (T : ℝ≥0∞) = D.U ω := ENNReal.coe_toNNReal htop
      have hc : ContinuousOn (D.Γ ω) (Iic T) := by
        have h := (hg.2.1.add (continuousOn_const (c := (D.y : ℂ)))).mono
          (fun t ht => hT ▸ ENNReal.coe_le_coe.2 ht)
        exact h.congr fun t _ => by
          change D.Γ ω t = D.Γ ω t - (D.y : ℂ) + D.y
          exact (sub_add_cancel _ _).symm
      have hf : η₀ ω = fun t => D.Γ ω (min t T) := funext fun t => by
        rw [heq, ← hT, ← ENNReal.coe_min, ENNReal.toNNReal_coe]
      rw [hf]
      exact hc.comp_continuous (continuous_id.min continuous_const)
        (fun t => by change min t T ≤ T; exact min_le_right _ _)
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  let η : S → ℝ≥0 → ℂ := fun ω t => if ω ∈ N then D.y else η₀ ω t
  refine ⟨η, fun t => Measurable.ite hNm measurable_const (hm t), fun ω => ?_, ?_⟩
  · by_cases hω : ω ∈ N
    · simpa only [η, hω, ↓reduceIte] using (continuous_const : Continuous fun _ : ℝ≥0 => (D.y : ℂ))
    · have hg : Continuous (η₀ ω) ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ D.U ω → η₀ ω t = D.Γ ω t :=
        not_not.1 (fun h => hω (hNsub h))
      simpa only [η, hω, ↓reduceIte] using hg.1
  · have hnae : ∀ᵐ ω ∂D.P, ω ∉ N := ae_iff.2 (by
      convert hN0 using 1
      congr 1
      ext ω
      simp only [mem_ofPred_eq, not_not])
    filter_upwards [hgood, hnae] with ω hg hn t ht
    simpa only [η, hn, ↓reduceIte] using hg.2 t ht

/-- A measurable trace version is adapted before the original lifetime.
The reader only uses the driver through the current deterministic time. -/
theorem measurableSet_trace_before {η : S → ℝ≥0 → ℂ}
    (hm : ∀ t, Measurable fun ω => η ω t)
    (hag : ∀ᵐ ω ∂D.P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ D.U ω → η ω t = D.Γ ω t)
    (t : ℝ≥0) {A : Set ℂ} (hA : MeasurableSet A) :
    MeasurableSet[D.driving t] {ω | (t : ℝ≥0∞) < D.U ω ∧ η ω t ∈ A} := by
  classical
  have ha : AdaptedBefore D.driving D.U D.W₀ := Ito.adaptedBefore_mono
    (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_W D.killed)
  have hlive : MeasurableSet[D.driving t] {ω | (t : ℝ≥0∞) < D.U ω} := by
    simpa only [mem_univ, and_true] using ha t univ MeasurableSet.univ
  let w : S → ℝ≥0 → ℝ := fun ω r => Girsanov.killed D.U D.W₀ (min r t) ω
  have hw : Measurable[D.driving t] w := @Measurable.of_eval S ℝ≥0 (fun _ => ℝ)
    (D.driving t) _ _ fun r =>
    (Girsanov.measurable_killed ha (min r t)).mono (D.driving.mono (min_le_right _ _)) le_rfl
  let R : S → ℂ := fun ω => (D.y : ℂ) + LP.traceAt t (w ω)
  have hR : Measurable[D.driving t] R := measurable_const.add ((LP.measurable_traceAt t).comp hw)
  have he : ∀ᵐ ω ∂D.P, (t : ℝ≥0∞) < D.U ω → R ω = η ω t := by
    filter_upwards [hag, D.trace, D.regular] with ω hω hg hp ht
    have heq : LP.traceAt t (w ω) = LP.traceAt t (D.W₀ · ω) :=
      LP.traceAt_congr fun r hr => by
        simp only [w, min_eq_left hr, Girsanov.killed_of_lt
          ((ENNReal.coe_le_coe.2 hr).trans_lt ht)]
    change (D.y : ℂ) + LP.traceAt t (w ω) = η ω t
    rw [heq, LP.traceAt_eq_of_isGeneratingTrace hg hp.1
      hp.2 ht, hω t ht.le]
    exact add_sub_cancel _ _
  apply WholeField.measurableSet_of_ae_eq (D.driving.le t)
    (fun N hN h0 => Ito.measurableSet_usualAugmentation_of_null hN h0 t)
    ((measurableSet_lt measurable_const (FlowStopIdentLift.measurable_lifetime D.killed)).inter (hm t hA))
    (hlive.inter (hR hA))
  filter_upwards [he] with ω hω
  apply propext
  constructor
  · rintro ⟨ht, hη⟩
    exact ⟨ht, by change R ω ∈ A; rw [hω ht]; exact hη⟩
  · rintro ⟨ht, hη⟩
    exact ⟨ht, by change η ω t ∈ A; rw [← hω ht]; exact hη⟩

/-- The available trace has an everywhere continuous, adapted extension,
including agreement at its finite lifetime. -/
theorem exists_continuous_adapted_trace :
    ∃ Z : ℝ≥0 → S → ℂ, (∀ ω, Z 0 ω = D.y) ∧ (∀ ω, Continuous (Z · ω)) ∧
      (∀ t, Measurable[D.driving t] (Z t)) ∧
      ∀ᵐ ω ∂D.P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ D.U ω → Z t ω = D.Γ ω t := by
  classical
  obtain ⟨η, hm, hc, hag⟩ := D.exists_continuous_measurable_trace
  let G : Set S := {ω | η ω 0 = (D.y : ℂ)}
  have hGm : MeasurableSet G := measurableSet_eq_fun (hm 0) measurable_const
  have hGae : ∀ᵐ ω ∂D.P, ω ∈ G := by
    filter_upwards [hag, D.trace] with ω hη hg
    exact (hη 0 bot_le).trans (sub_eq_zero.1 hg.1)
  let Y : S → ℝ≥0 → ℂ := fun ω t => if ω ∈ G then η ω t else D.y
  have hYm : ∀ t, Measurable fun ω => Y ω t := fun t => (hm t).ite hGm measurable_const
  have hYc : ∀ ω, Continuous (Y ω) := by
    intro ω
    by_cases hω : ω ∈ G
    · simpa only [Y, hω, ↓reduceIte] using hc ω
    · simp only [Y, hω, ↓reduceIte]; exact continuous_const
  have hY0 : ∀ ω, Y ω 0 = D.y := by
    intro ω
    by_cases hω : ω ∈ G
    · exact (ite_eq_left hω).trans hω
    · exact ite_eq_right hω
  have hYag : ∀ᵐ ω ∂D.P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ D.U ω → Y ω t = D.Γ ω t := by
    filter_upwards [hGae, hag] with ω hG hη t ht
    exact (ite_eq_left hG).trans (hη t ht)
  have haR : AdaptedBefore D.driving D.U (fun t ω => (Y ω t).re - D.y) := by
    intro t A hA
    exact D.measurableSet_trace_before hYm hYag t
      ((Complex.continuous_re.sub continuous_const).measurable hA)
  have haI : AdaptedBefore D.driving D.U (fun t ω => (Y ω t).im) := by
    intro t A hA
    exact D.measurableSet_trace_before hYm hYag t (Complex.continuous_im.measurable hA)
  obtain ⟨R, hR0, hRc, hRa, hRag⟩ := RetAux79.exists_continuous_adapted_stopped
    (X := fun t ω => (Y ω t).re - D.y)
    (fun ω => (Complex.continuous_re.comp (hYc ω)).sub continuous_const)
    (fun ω => by rw [hY0]; simp only [Complex.ofReal_re, sub_self]) haR
  obtain ⟨I, hI0, hIc, hIa, hIag⟩ := RetAux79.exists_continuous_adapted_stopped
    (X := fun t ω => (Y ω t).im)
    (fun ω => Complex.continuous_im.comp (hYc ω))
    (fun ω => by rw [hY0]; exact Complex.ofReal_im _) haI
  let Z : ℝ≥0 → S → ℂ := fun t ω => ((D.y + R t ω : ℝ) : ℂ) + (I t ω : ℂ) * Complex.I
  have hZc : ∀ ω, Continuous (Z · ω) := fun ω =>
    (Complex.continuous_ofReal.comp (continuous_const.add (hRc ω))).add
      ((Complex.continuous_ofReal.comp (hIc ω)).mul continuous_const)
  have hZ0 : ∀ ω, Z 0 ω = D.y := fun ω => by
    simp only [Z, hR0, hI0, add_zero, Complex.ofReal_zero, zero_mul]
  have hZY : ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) < D.U ω → Z t ω = Y ω t := by
    intro ω t ht
    apply Complex.ext
    · simp only [Z, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, hRag ω t ht]
      ring
    · simp only [Z, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add, hIag ω t ht]
  refine ⟨Z, hZ0, hZc, fun t =>
    (Complex.measurable_ofReal.comp (measurable_const.add (hRa t).measurable)).add
      ((Complex.measurable_ofReal.comp (hIa t).measurable).mul measurable_const), ?_⟩
  filter_upwards [hYag] with ω hω t ht
  refine Eq.trans ?_ (hω t ht)
  by_cases ht0 : t = 0
  · subst t
    exact (hZ0 ω).trans (hY0 ω).symm
  · have htpos : 0 < t := pos_iff_ne_zero.2 ht0
    have : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, htpos⟩
    have hz : Tendsto (Z · ω) (𝓝[<] t) (𝓝 (Z t ω)) :=
      (hZc ω).tendsto t |>.mono_left nhdsWithin_le_nhds
    have hy : Tendsto (Y ω) (𝓝[<] t) (𝓝 (Y ω t)) :=
      (hYc ω).tendsto t |>.mono_left nhdsWithin_le_nhds
    have heq : (Y ω) =ᶠ[𝓝[<] t] (Z · ω) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (hZY ω s ((ENNReal.coe_lt_coe.2 hs).trans_le ht)).symm
    exact tendsto_nhds_unique hz (hy.congr' heq)

end ClockSource
end InteractingSLE.Sec5.Aux61R45
