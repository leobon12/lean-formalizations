import SupercriticalLQGUniqueness.B2.PfeWeyl.S1Decompose
import SupercriticalLQGUniqueness.B2.PfeWeyl.InputsS1

 





















set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric (DistC addFun IsGFFPlusBddCont)
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 

theorem tendsto_normalizedLFPP_iff_lscTendsto (ξ : ℝ) (a : ℕ → Set.Ioi (0 : ℝ))
    (φ : ℕ → C(ℂ, ℝ)) (E : LSCMetric) :
    Tendsto (fun n => normalizedLFPPMetric ξ (a n) (φ n)) atTop (𝓝 E) ↔
      LSCTendsto (fun n => rescaledLFPP ξ (a n) (φ n)) E.toLSCFun.1 := by
  rw [LSCMetric.isInducing_toLSCFun.tendsto_nhds_iff, LSCFun.tendsto_iff_lscTendsto]
  have hfun : (fun n => ((normalizedLFPPMetric ξ (a n) (φ n)).toLSCFun).1) =
      fun n => rescaledLFPP ξ (a n) (φ n) := by
    funext n
    funext p
    exact normalizedLFPPMetric_toLSCFun ξ (a n) (φ n) p
  change LSCTendsto (fun n => ((normalizedLFPPMetric ξ (a n) (φ n)).toLSCFun).1) _ ↔ _
  rw [hfun]

 

theorem ae_forall_rationalCircle {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (u : ℕ → Ω → Set ℂ → Set ℂ → ℝ≥0∞) (v : Ω → Set ℂ → Set ℂ → ℝ≥0∞)
    (h : ∀ O O' : Set ℂ, IsRationalCircle O → IsRationalCircle O' →
      ∀ᵐ ω ∂P, Tendsto (fun n => u n ω O O') atTop (𝓝 (v ω O O'))) :
    ∀ᵐ ω ∂P, ∀ O O' : Set ℂ, IsRationalCircle O → IsRationalCircle O' →
      Tendsto (fun n => u n ω O O') atTop (𝓝 (v ω O O')) := by
  let circ : ℚ × ℚ × ℚ → Set ℂ := fun c =>
    Metric.sphere (Complex.mk (c.1 : ℝ) (c.2.1 : ℝ)) (c.2.2 : ℝ)
  have hpair : ∀ c c' : ℚ × ℚ × ℚ, ∀ᵐ ω ∂P, 0 ≤ c.2.2 → 0 ≤ c'.2.2 →
      Tendsto (fun n => u n ω (circ c) (circ c')) atTop (𝓝 (v ω (circ c) (circ c'))) := by
    intro c c'
    by_cases hc : 0 ≤ c.2.2
    · by_cases hc' : 0 ≤ c'.2.2
      · filter_upwards [h (circ c) (circ c') ⟨c.1, c.2.1, c.2.2, hc, rfl⟩
          ⟨c'.1, c'.2.1, c'.2.2, hc', rfl⟩] with ω hω _ _
        exact hω
      · exact Eventually.of_forall fun ω _ h' => absurd h' hc'
    · exact Eventually.of_forall fun ω h' _ => absurd h' hc
  filter_upwards [ae_all_iff.2 fun c => ae_all_iff.2 fun c' => hpair c c'] with ω hω
    O O' hO hO'
  obtain ⟨x, y, r, hr, rfl⟩ := hO
  obtain ⟨x', y', r', hr', rfl⟩ := hO'
  exact hω (x, y, r) (x', y', r') hr hr'

 

theorem boundedShiftWeyl_of_isPfeWeakMetric {ξ : Set.Ioi (0 : ℝ)} {D : DistC → LSCMetric}
    {c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)} (hD : IsPfeWeakMetric ξ D c) :
    BoundedShiftWeyl ξ D := by
  intro Ω _ P _ h hh F _ _
  filter_upwards [hD.2.2.2.1 P h (LQGMetric.GM.isGFFPlusCont_of_isWholePlaneGFF hh.1)]
    with ω hω
  exact (hω (F ω)).symm

 
theorem subseqLimit_of_normalized_of_inputs
    (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (D : DistC → LSCMetric)
    (hnorm : SubseqLimitNormalized ξ m ε D) (hgeo : NormalizedLimitGeometry D)
    (htail : NormalizedAcrossTails D) (hsmall : NormalizedSmallAnnuli ξ m ε D)
    (hweyl : BoundedShiftWeyl ξ D) :
    SubseqLimit ξ m ε D := by
  intro Ω _ P _ h' hh' Y hY
  obtain ⟨k, F, hk, hF, hFb, hdec⟩ := exists_normalized_bdd_decomposition hh'
  have hkb : IsGFFPlusBddCont k P := LQGMetric.DFGPS.isGFFPlusBddCont_of_wp hk.1
  have hXex : ∀ δ : Set.Ioi (0 : ℝ), ∃ X : Ω → C(ℂ, ℝ), IsHeatSmoothing P k δ X :=
    fun δ => (PfeAxioms.exists_heatVersion_bdd hkb δ).imp fun _ hX => hX.2
  choose X hX using hXex
  have hFb' := hFb
  choose Mf hMf using hFb'
  have hh'eq : h' = fun ω => addFun (k ω) (F ω) := funext hdec
  subst hh'eq
  obtain ⟨hlimk, hcirck⟩ := hnorm P k hk X hX
  have hconvk : ∀ᵐ ω ∂P, Tendsto (fun n =>
      normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (X (ε n) ω)) atTop (𝓝 (D (k ω))) := by
    filter_upwards [hlimk] with ω hω
    exact (tendsto_normalizedLFPP_iff_lscTendsto _ _ _ _).2 hω
  have hcircω : ∀ᵐ ω ∂P, ∀ O O' : Set ℂ, IsRationalCircle O → IsRationalCircle O' →
      Tendsto (fun n => setDistance (normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (X (ε n) ω)) O O')
        atTop (𝓝 (setDistance (D (k ω)) O O')) := by
    refine ae_forall_rationalCircle P
      (fun n ω O O' => setDistance (normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (X (ε n) ω)) O O')
      (fun ω O O' => setDistance (D (k ω)) O O') fun O O' hO hO' => ?_
    filter_upwards [hcirck O O' hO hO'] with ω hω
    simp only [setDistance_normalizedLFPPMetric]
    exact hω
  obtain ⟨hlen, hctrl⟩ := hgeo P k hk
  have hbase := ae_weyl_scaling_all_bounded_of_tendsto ξ m ε hε P (fun ω => D (k ω)) X
    hconvk hlen hctrl (htail P k hk) (hsmall P k hk X hX)
  have hbasec := ae_weyl_rationalCircle_all_bounded_of_tendsto ξ m ε hε P
    (fun ω => D (k ω)) X hconvk hcircω hlen hctrl (htail P k hk) (hsmall P k hk X hX)
  have hshift := ae_heatVersion_shift_eq ε P k hk F Mf hMf hh' X Y hX hY
  have hW := hweyl P k hk F hF hFb
  refine ⟨?_, fun O O' hO hO' => ?_⟩
  · filter_upwards [hbase, hshift, hW] with ω hb hs hw
    obtain ⟨E, hE, hconv⟩ := hb (F ω) (Mf ω) (hMf ω)
    have hseq : (fun n => normalizedLFPPMetric (ξ : ℝ) (m (ε n))
        (X (ε n) ω + LQGMetric.LFPP.mollCont (ε n : ℝ) (ε n).property.ne' (F ω) (Mf ω)
          (hMf ω))) = fun n => normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (Y (ε n) ω) := by
      funext n
      rw [hs n]
    rw [hseq] at hconv
    have hED : E = D (addFun (k ω) (F ω)) := LSCMetric.ext fun p => by
      rw [hE p]
      exact (congrFun hw p).symm
    rw [hED] at hconv
    exact (tendsto_normalizedLFPP_iff_lscTendsto _ _ _ _).1 hconv
  · filter_upwards [hbasec, hshift, hW] with ω hb hs hw
    have hc := hb (F ω) (Mf ω) (hMf ω) O O' hO hO'
    have hseq : (fun n => setDistance (normalizedLFPPMetric (ξ : ℝ) (m (ε n))
        (X (ε n) ω + LQGMetric.LFPP.mollCont (ε n : ℝ) (ε n).property.ne' (F ω) (Mf ω)
          (hMf ω))) O O') = fun n => ENNReal.ofReal ((m (ε n) : ℝ)⁻¹) *
            setDistance (lfppDistance (ξ : ℝ) (Y (ε n) ω)) O O' := by
      funext n
      rw [hs n, setDistance_normalizedLFPPMetric]
    rw [hseq, ← hw] at hc
    exact hc

 
theorem subseqLimit_of_normalized_of_pfeWeak
    (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (D : DistC → LSCMetric) (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (hPfe : IsPfeWeakMetric ξ D c)
    (hnorm : SubseqLimitNormalized ξ m ε D) (hgeo : NormalizedLimitGeometry D)
    (htail : NormalizedAcrossTails D) (hsmall : NormalizedSmallAnnuli ξ m ε D) :
    SubseqLimit ξ m ε D :=
  subseqLimit_of_normalized_of_inputs ξ m ε hε D hnorm hgeo htail hsmall
    (boundedShiftWeyl_of_isPfeWeakMetric hPfe)

end SupercriticalLQGUniqueness.B2.PfeWeyl
