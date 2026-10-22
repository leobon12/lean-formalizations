import HigherDimLQGMetric.Freq.Arithmetic
import HigherDimLQGMetric.Metric.Reparam

/-!
# Arc length for a geodesic crossing

The natural parameterization from the generic metric geometry layer keeps the
image of a finite path and exposes its subinterval lengths.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set LQGMetric.MetricGeometry
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- Reparametrize a geodesic by its metric arc length, retaining its image. -/
theorem s4c_geodesic_arclength (D : ContMetric d) (P : ℝ → Rd d)
    (hP : IsGeod D P) (S : Set (Rd d)) (hPS : ∀ τ ∈ Icc (0 : ℝ) 1, P τ ∈ S) :
    ∃ Q : ℝ → Rd d,
      ContinuousOn Q (Icc 0 (D.1 (P 0, P 1))) ∧
      Q 0 = P 0 ∧ Q (D.1 (P 0, P 1)) = P 1 ∧
      (∀ s ∈ Icc 0 (D.1 (P 0, P 1)), Q s ∈ S) ∧
      (∀ s ∈ Icc 0 (D.1 (P 0, P 1)), ∀ t ∈ Icc 0 (D.1 (P 0, P 1)), s ≤ t →
        D.len Q s t = ENNReal.ofReal (t - s) ∧
        ENNReal.ofReal (D.1 (Q s, Q t)) = ENNReal.ofReal (t - s)) := by
  let L := D.1 (P 0, P 1)
  have hL : 0 ≤ L := D.nonneg _ _
  let Pm : ℝ → D.Space := D.pt ∘ P
  have hPc : ContinuousOn Pm (Icc 0 1) := D.continuous_pt.comp_continuousOn hP.1
  have hPlen : curveLength Pm 0 1 = ENNReal.ofReal L := hP.2
  have hfin : curveLength Pm 0 1 ≠ ∞ := by rw [hPlen]; exact ENNReal.ofReal_ne_top
  have hPmem : MapsTo Pm (Icc 0 1) (D.pt '' S) := by
    intro u hu
    exact ⟨P u, hPS u hu, rfl⟩
  let R := lengthParam Pm 0 1
  have hprops := lengthParam_props zero_le_one hPc hfin hPmem
  have hLt : (curveLength Pm 0 1).toReal = L := by
    rw [hPlen, ENNReal.toReal_ofReal hL]
  let Q : ℝ → Rd d := D.unpt ∘ R
  have hcont : ContinuousOn Q (Icc 0 L) := by
    exact D.continuous_unpt.comp_continuousOn (hLt ▸ hprops.2.1)
  have hQ0 : Q 0 = P 0 := by
    change D.unpt (R 0) = P 0
    have hR0 : R 0 = Pm 0 := hprops.2.2.1
    rw [hR0]
    exact D.unpt_pt _
  have hQL : Q L = P 1 := by
    change D.unpt (R L) = P 1
    have hRL : R (curveLength Pm 0 1).toReal = Pm 1 := hprops.2.2.2.1
    rw [← hLt, hRL]
    exact D.unpt_pt _
  have hQS : ∀ s ∈ Icc 0 L, Q s ∈ S := by
    intro s hs
    obtain ⟨u, hu, heq⟩ := hprops.2.2.2.2 (hLt ▸ hs)
    change D.unpt (R s) ∈ S
    change D.pt u = R s at heq
    rw [← heq, D.unpt_pt]
    exact hu
  have hRgeo : IsGeodesicCurve R 0 L := by
    refine ⟨hL, hLt ▸ hprops.2.1, ?_⟩
    change curveLength R 0 L = edist (R 0) (R L)
    have hR0 : R 0 = Pm 0 := hprops.2.2.1
    have hRL : R (curveLength Pm 0 1).toReal = Pm 1 := hprops.2.2.2.1
    have hRL' : R L = Pm 1 := hLt ▸ hRL
    rw [hR0, hRL']
    calc
      curveLength R 0 L = curveLength Pm 0 1 := by
        rw [← hLt]
        exact curveLength_lengthParam zero_le_one hPc hfin
      _ = edist (Pm 0) (Pm 1) := by
        rw [hPlen]
        exact (D.edist_pt (P 0) (P 1)).symm
  refine ⟨Q, hcont, hQ0, hQL, hQS, ?_⟩
  intro s hs t ht hst
  have hu : HasUnitSpeedOn R (Icc 0 L) := hLt ▸ hprops.1
  have hlen := curveLength_of_hasUnitSpeedOn hu hs ht
  have hdist := hRgeo.edist_eq_of_hasUnitSpeedOn hu hs ht hst
  constructor
  · change curveLength R s t = ENNReal.ofReal (t - s)
    exact hlen
  · rw [← D.edist_pt (Q s) (Q t)]
    change edist (R s) (R t) = ENNReal.ofReal (t - s)
    exact hdist

/-- An affine restriction of a unit-speed geodesic is an internal geodesic in
any open region that contains its image. -/
theorem s4c_affinePiece (D : ContMetric d) (Q : ℝ → Rd d) (S V : Set (Rd d))
    {L a b : ℝ} (hQa : 0 ≤ a) (hab : a ≤ b) (hbL : b ≤ L)
    (hQc : ContinuousOn Q (Icc 0 L)) (hQS : ∀ s ∈ Icc a b, Q s ∈ S)
    (hSV : S ⊆ V)
    (hQlen : D.len Q a b = ENNReal.ofReal (b - a))
    (hQdist : ENNReal.ofReal (D.1 (Q a, Q b)) = ENNReal.ofReal (b - a)) :
    ∃ R : ℝ → Rd d,
      IsGeodIn D V R ∧ (∀ τ ∈ Icc (0 : ℝ) 1, R τ ∈ S) ∧
      R 0 = Q a ∧ R 1 = Q b ∧ D.len R 0 1 = ENNReal.ofReal (b - a) := by
  let φ : ℝ → ℝ := fun τ => a + τ * (b - a)
  have hφmono : MonotoneOn φ (Icc (0 : ℝ) 1) := by
    intro s _ t _ hst
    change a + s * (b - a) ≤ a + t * (b - a)
    simpa only [add_comm] using
      (add_le_add_left (mul_le_mul_of_nonneg_right hst (sub_nonneg.mpr hab)) a)
  have hφcont : ContinuousOn φ (Icc (0 : ℝ) 1) :=
    ((continuous_const.add (continuous_id.mul continuous_const)).continuousOn)
  have hφimg : φ '' Icc (0 : ℝ) 1 = Icc a b := by
    have hi := hφcont.image_Icc_of_monotoneOn zero_le_one hφmono
    convert hi using 1; simp [φ]
  have hφmaps : MapsTo φ (Icc (0 : ℝ) 1) (Icc 0 L) := by
    intro τ hτ
    have hτab : φ τ ∈ Icc a b := hφimg ▸ ⟨τ, hτ, rfl⟩
    exact ⟨hQa.trans hτab.1, hτab.2.trans hbL⟩
  let R : ℝ → Rd d := Q ∘ φ
  have hRc : ContinuousOn R (Icc (0 : ℝ) 1) := hQc.comp hφcont hφmaps
  have hRS : ∀ τ ∈ Icc (0 : ℝ) 1, R τ ∈ S := by
    intro τ hτ
    exact hQS (φ τ) (hφimg ▸ ⟨τ, hτ, rfl⟩)
  have hR0 : R 0 = Q a := by simp [R, φ]
  have hR1 : R 1 = Q b := by simp [R, φ]
  have hRlen : D.len R 0 1 = ENNReal.ofReal (b - a) := by
    rw [D.len_def]
    have hcomp : (D.pt ∘ R) = (D.pt ∘ Q) ∘ φ := rfl
    rw [hcomp, curveLength_comp_of_monotoneOn _ hφmono hφimg]
    exact hQlen
  have hRint : D.internal V (R 0) (R 1) = D.len R 0 1 := by
    apply le_antisymm
    · exact D.internal_le_len zero_le_one hRc (fun τ hτ => hSV (hRS τ hτ))
    · rw [hRlen, ← hQdist, hR0, hR1]
      exact D.ofReal_le_internal V _ _
  exact ⟨R, ⟨hRc, (fun τ hτ => hSV (hRS τ hτ)), hRint.symm⟩, hRS,
    hR0, hR1, hRlen⟩

end HigherDimLQGMetric
