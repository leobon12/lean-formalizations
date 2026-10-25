import SupercriticalLQGUniqueness.B2.PfeLocal.L4Main
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.PathInfimum.PathInf
import LQGMetric.Blueprint.M2Defs

 






















set_option autoImplicit false
noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal
open LQGMetric (CondIndepEv DistC)

namespace SupercriticalLQGUniqueness.B2.PfeLocal

open Uniqueness.Toolkit.CompactPathInfimum

 

abbrev L5Code : Type := (ℚ × ℚ × ℚ × ℚ) × (ℚ × ℚ × ℚ) × (ℚ × ℚ × ℚ)

 
def l5Rect (q : ℚ × ℚ × ℚ × ℚ) : Set ℂ :=
  {z | (q.1 : ℝ) ≤ z.re ∧ z.re ≤ q.2.1 ∧ (q.2.2.1 : ℝ) ≤ z.im ∧ z.im ≤ q.2.2.2}

 
def l5Ball (q : ℚ × ℚ × ℚ) : Set ℂ := Metric.closedBall ⟨q.1, q.2.1⟩ (q.2.2 : ℝ)

theorem l5Rect_isCompact (q : ℚ × ℚ × ℚ × ℚ) : IsCompact (l5Rect q) := by
  have : l5Rect q = Complex.equivRealProdCLM.symm '' (Icc (q.1 : ℝ) q.2.1 ×ˢ
      Icc (q.2.2.1 : ℝ) q.2.2.2) := by
    ext z
    simp only [l5Rect, mem_setOf_eq, mem_image, mem_prod, mem_Icc]
    constructor
    · intro hz
      exact ⟨(z.re, z.im), ⟨⟨hz.1, hz.2.1⟩, hz.2.2.1, hz.2.2.2⟩, by
        apply Complex.ext <;> simp⟩
    · rintro ⟨p, ⟨⟨h1, h2⟩, h3, h4⟩, rfl⟩
      simp only [Complex.equivRealProdCLM_symm_apply_re, Complex.equivRealProdCLM_symm_apply_im]
      exact ⟨h1, h2, h3, h4⟩
  rw [this]
  exact (isCompact_Icc.prod isCompact_Icc).image Complex.equivRealProdCLM.symm.continuous

theorem l5Ball_isCompact (q : ℚ × ℚ × ℚ) : IsCompact (l5Ball q) :=
  isCompact_closedBall _ _

 
def l5Obs (D : LSCMetric) (c : L5Code) : ℝ≥0∞ :=
  compactPathInf D (l5Rect c.1) (l5Ball c.2.1) (l5Ball c.2.2)

theorem measurable_l5Obs (c : L5Code) : Measurable fun D : LSCMetric => l5Obs D c :=
  compactPathInf_measurable (l5Rect_isCompact _) (l5Ball_isCompact _) (l5Ball_isCompact _)

 
def l5ObsSigma {Ω : Type} (L : Ω → LSCMetric) (V : Set ℂ) : MeasurableSpace Ω :=
  ⨆ (c : L5Code) (_ : l5Rect c.1 ⊆ V),
    MeasurableSpace.comap (fun ω => l5Obs (L ω) c) inferInstance

theorem l5ObsSigma_mono {Ω : Type} (L : Ω → LSCMetric) {V W : Set ℂ} (hVW : V ⊆ W) :
    l5ObsSigma L V ≤ l5ObsSigma L W :=
  iSup₂_le fun c hc => le_iSup₂_of_le (f := fun (c : L5Code) (_ : l5Rect c.1 ⊆ W) =>
    MeasurableSpace.comap (fun ω => l5Obs (L ω) c) inferInstance) c (hc.trans hVW) le_rfl

theorem l5ObsSigma_le {Ω : Type} [mΩ : MeasurableSpace Ω] {L : Ω → LSCMetric}
    (hL : Measurable L) (V : Set ℂ) : l5ObsSigma L V ≤ mΩ :=
  iSup₂_le fun c _ => ((measurable_l5Obs c).comp hL).comap_le

namespace Inputs

 



def L5ObsLocality {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistC)
    (L : Ω → LSCMetric) : Prop :=
  ∀ V : TopologicalSpace.Opens ℂ,
    CondIndepEv (LQGMetric.Blueprint.fieldSigma h V) (l5ObsSigma L V)
      (LQGMetric.Blueprint.fieldSigmaClosed h (V : Set ℂ)ᶜ ⊔
        l5ObsSigma L (closure (V : Set ℂ))ᶜ) P

end Inputs

 
def l5Enc (S : Set ℂ) (D : LSCMetric) : L5Code → ℝ≥0∞ := fun c => by
  classical exact if l5Rect c.1 ⊆ S then l5Obs D c else 0

theorem measurable_l5Enc (S : Set ℂ) : Measurable (l5Enc S) := by
  classical
  refine measurable_pi_iff.2 fun c => ?_
  by_cases hc : l5Rect c.1 ⊆ S
  · simpa only [l5Enc, hc, if_true] using measurable_l5Obs c
  · simpa only [l5Enc, hc, if_false] using measurable_const

theorem l5Enc_of_subset {S : Set ℂ} (D : LSCMetric) {c : L5Code} (hc : l5Rect c.1 ⊆ S) :
    l5Enc S D c = l5Obs D c := by
  classical
  simp only [l5Enc, hc, if_true]

theorem l5_comap_enc_le {Ω : Type} (L : Ω → LSCMetric) (S : Set ℂ) :
    MeasurableSpace.comap (fun ω => l5Enc S (L ω)) inferInstance ≤ l5ObsSigma L S := by
  classical
  rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  refine iSup_le fun c => ?_
  rw [MeasurableSpace.comap_comp]
  by_cases hc : l5Rect c.1 ⊆ S
  · have : ((fun f : L5Code → ℝ≥0∞ => f c) ∘ fun ω => l5Enc S (L ω)) =
        fun ω => l5Obs (L ω) c := by
      funext ω; simp only [Function.comp_apply, l5Enc, hc, if_true]
    rw [this]
    exact le_iSup₂_of_le (f := fun (c : L5Code) (_ : l5Rect c.1 ⊆ S) =>
      MeasurableSpace.comap (fun ω => l5Obs (L ω) c) inferInstance) c hc le_rfl
  · have : ((fun f : L5Code → ℝ≥0∞ => f c) ∘ fun ω => l5Enc S (L ω)) = fun _ => 0 := by
      funext ω; simp only [Function.comp_apply, l5Enc, hc, if_false]
    rw [this]
    rw [MeasurableSpace.comap_const]; exact bot_le

end SupercriticalLQGUniqueness.B2.PfeLocal
