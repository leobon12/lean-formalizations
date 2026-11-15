/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofFinalNoncollision

/-!
# Measurable continuous extensions of the closed retained trace

Packet PROVE-RETPLUMB. Canonical code transport requires globally continuous
coordinates. The existing dyadic stopped reader supplies them from continuity
only through the closed lifetime, including its value at a finite endpoint.
-/
set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
namespace InteractingSLE.Restart.RetAux79
open Sec7
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

omit mΩ in
/-- The existing scalar stopped reader agrees through the closed lifetime and
is globally continuous; no post-lifetime continuity of the raw coordinate is used. -/
theorem stopVal_closed_spec {V : Ω → ℝ≥0∞} {X : ℝ≥0 → Ω → ℝ}
    (hc : ∀ ω, ContinuousOn (X · ω) {t | (t : ℝ≥0∞) ≤ V ω})
    (h0 : ∀ ω, X 0 ω = 0) (ω : Ω) :
    Continuous (LocalExt.stopVal X (fun ω => (V ω : WithTop ℝ≥0)) · ω) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ V ω →
        LocalExt.stopVal X (fun ω => (V ω : WithTop ℝ≥0)) t ω = X t ω := by
  classical
  let S : Ω → WithTop ℝ≥0 := fun ω => (V ω : WithTop ℝ≥0)
  by_cases hz : V ω = 0
  · have hS : S ω = 0 := hz
    have he : ∀ t, LocalExt.stopVal X S t ω = 0 := by
      intro t
      have hn (q : ℝ≥0) : ¬ (q : WithTop ℝ≥0) < 0 := by exact_mod_cast (not_lt_zero : ¬ q < 0)
      have hl : (fun n => LocalExt.lowVal X S n ω) = fun _ => 0 := by
        funext n
        rw [LocalExt.lowVal, hS, ite_eq_right (hn _)]
      rw [LocalExt.stopVal, hS, ite_eq_right (hn t), hl]
      exact (tendsto_const_nhds (x := (0 : ℝ))).limUnder_eq
    refine ⟨?_, ?_⟩
    · have hef : (LocalExt.stopVal X S · ω) = fun _ => 0 := funext he
      change Continuous (LocalExt.stopVal X S · ω)
      rw [hef]
      exact continuous_const
    intro t ht
    have ht0 : t = 0 := ENNReal.coe_eq_zero.1 (le_zero_iff.1 (hz ▸ ht))
    rw [he, ht0, h0]
  by_cases htop : V ω = ⊤
  · have he : ∀ t, LocalExt.stopVal X S t ω = X t ω := by
      intro t
      exact ite_eq_left (by change (t : WithTop ℝ≥0) < (V ω : WithTop ℝ≥0); rw [htop]; exact WithTop.coe_lt_top t)
    refine ⟨?_, fun t _ => he t⟩
    have hc' : Continuous (X · ω) := by
      apply continuousOn_univ.1
      simpa only [htop, le_top, ofPred_true] using hc ω
    have hef : (LocalExt.stopVal X S · ω) = (X · ω) := funext he
    change Continuous (LocalExt.stopVal X S · ω)
    rw [hef]
    exact hc'
  let T := (V ω).toNNReal
  have he : (T : ℝ≥0∞) = V ω := ENNReal.coe_toNNReal htop
  have hpos : 0 < V ω := pos_iff_ne_zero.2 hz
  have hT : 0 < T := ENNReal.coe_pos.1 (he.symm ▸ hpos)
  have hs : S ω = T := by
    change (V ω : WithTop ℝ≥0) = _
    rw [← he]
    rfl
  have hcT : ContinuousOn (X · ω) (Iio T) := (hc ω).mono fun t ht => by
    change (t : ℝ≥0∞) ≤ V ω
    rw [← he]
    exact ENNReal.coe_le_coe.2 ht.le
  have hlim : Tendsto (X · ω) (𝓝[<] T) (𝓝 (X T ω)) :=
    ((hc ω T he.le).mono fun t ht => (ENNReal.coe_le_coe.2 ht.le).trans he.le)
  refine ⟨FlowStopIdentLL.continuous_stopVal_of_tendsto hT hs hcT hlim, ?_⟩
  intro t ht
  rw [LocalExt.stopVal_eq (S := S) hpos htop (hc ω), stopAt_of_eq_coe hs]
  have htT : t ≤ T := ENNReal.coe_le_coe.1 (ht.trans_eq he.symm)
  rw [min_eq_left htT]

/-- Scalar stopped coordinates are ambient measurable from measurable lifetime
and deterministic coordinates, using the constant full-information filtration. -/
theorem measurable_stopVal_of_coordinates {V : Ω → ℝ≥0∞} {X : ℝ≥0 → Ω → ℝ}
    (hV : Measurable V) (hX : ∀ t, Measurable (X t)) (t : ℝ≥0) :
    Measurable (LocalExt.stopVal X (fun ω => (V ω : WithTop ℝ≥0)) t) := by
  let 𝓕 : Filtration ℝ≥0 mΩ := Filtration.const ℝ≥0 mΩ le_rfl
  have hs : IsStoppingTime 𝓕 (fun ω => (V ω : WithTop ℝ≥0)) := by
    intro t
    change MeasurableSet {ω | V ω ≤ (t : ℝ≥0∞)}
    exact measurableSet_le hV measurable_const
  exact LocalExt.measurable_stopVal_le hs
    (MartChar.adaptedBefore_of_stronglyAdapted hs (fun t => (hX t).stronglyMeasurable)) t

/-- A measurable globally continuous extension of a zero-start complex trace. -/
def retClosedTrace (V : Ω → ℝ≥0∞) (γ : Ω → ℝ≥0 → ℂ) (ω : Ω) (t : ℝ≥0) : ℂ :=
  ⟨LocalExt.stopVal (fun t ω => (γ ω t).re) (fun ω => (V ω : WithTop ℝ≥0)) t ω,
    LocalExt.stopVal (fun t ω => (γ ω t).im) (fun ω => (V ω : WithTop ℝ≥0)) t ω⟩

theorem retClosedTrace_data {V : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
    (hV : Measurable V) (hm : ∀ t, Measurable fun ω => γ ω t)
    (hc : ∀ ω, ContinuousOn (γ ω) {t | (t : ℝ≥0∞) ≤ V ω})
    (h0 : ∀ ω, γ ω 0 = 0) :
    (∀ t, Measurable fun ω => retClosedTrace V γ ω t) ∧
      (∀ ω, Continuous (retClosedTrace V γ ω)) ∧
      ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) ≤ V ω → retClosedTrace V γ ω t = γ ω t := by
  have hR := stopVal_closed_spec (fun ω => Complex.continuous_re.comp_continuousOn (hc ω))
    (fun ω => by simp [h0 ω])
  have hI := stopVal_closed_spec (fun ω => Complex.continuous_im.comp_continuousOn (hc ω))
    (fun ω => by simp [h0 ω])
  refine ⟨fun t => ?_, fun ω => ?_, fun ω t ht => ?_⟩
  · convert ((Complex.measurable_ofReal.comp
        (measurable_stopVal_of_coordinates hV (fun t => Complex.measurable_re.comp (hm t)) t)).add
        ((Complex.measurable_ofReal.comp
          (measurable_stopVal_of_coordinates hV (fun t => Complex.measurable_im.comp (hm t)) t)).mul_const Complex.I)) using 1
    funext ω
    apply Complex.ext <;> simp [retClosedTrace, Function.comp_def]
  · change Continuous (fun t => retClosedTrace V γ ω t)
    convert ((Complex.continuous_ofReal.comp (hR ω).1).add
        ((Complex.continuous_ofReal.comp (hI ω).1).mul_const Complex.I)) using 1
    funext t
    apply Complex.ext <;> simp [retClosedTrace, Function.comp_def]
  · exact Complex.ext ((hR ω).2 t ht) ((hI ω).2 t ht)

end InteractingSLE.Restart.RetAux79
