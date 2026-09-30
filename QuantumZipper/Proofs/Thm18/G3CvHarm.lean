import QuantumZipper.Proofs.Thm18.G3CvFub
import QuantumZipper.Proofs.GFF.K3.HarmonicPart

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3-CURVE, piece 1i: the harmonic part of the pulled-back field is harmonic

For a free field `W` and a continuous version `Y` of the pulled-back harmonic increments
`z ↦ W(Φ_*P_z) − W(Φ_*P_b)` (`pullIncr`), almost surely `Y ∘ foldH` has the circle mean-value
property on `ball b r₁` (`ae_meanValue_pullY`: stochastic Fubini `pull_stochFubini` against the
folded circle and `bind_foldedCircle_halfDiscPoisson`), hence is harmonic there
(`ae_harmonicOnNhd_pullY`, Weyl's lemma `harmonicOnNhd_of_meanValue`). Copy of the free-field
argument `ae_meanValue_harmH`/`ae_harmonicOnNhd_harmH` (HarmonicPart.lean) for the pull-back.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Filter Set
open scoped ComplexConjugate ENNReal Topology

namespace QuantumZipper
namespace G3Cv

open K3

variable {Φ : ℂ → ℂ} {b r₀ ρ r₁ m M : ℝ}

section
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : Ω → FieldSample} {Y : ℂ → Ω → ℝ}

theorem ae_meanValue_pullY (hW : IsFreeGFFModConstH W P) (hD : PullData Φ b r₀ ρ r₁ m M)
    (hr₁0 : 0 < r₁) (hYc : ∀ ω, ContinuousOn (fun z => Y z ω) Hbar)
    (hY : ∀ z ∈ Hbar, Y z =ᵐ[P] pullIncr W Φ b ρ r₁ z) {z : ℂ} {s : ℝ} (hs : 0 < s)
    (hzs : ‖z - b‖ + s < r₁) :
    ∀ᵐ ω ∂P, ∫ w, Y (foldH w) ω ∂circleUnif z s = Y (foldH z) ω := by
  have hρ := hD.hρ
  set ν := foldedCircle z s with hνdef
  set K := closedBall (b : ℂ) r₁ ∩ Hbar with hK_def
  have hKm : MeasurableSet K := isClosed_closedBall.measurableSet.inter isClosed_Hbar.measurableSet
  have hνK : ∀ᵐ x ∂ν, x ∈ K := by
    rw [hνdef, foldedCircle]
    refine (ae_map_iff measurable_foldH.aemeasurable hKm).2 ?_
    filter_upwards [ae_mem_sphere_circleUnif_k3 z hs] with w hw
    refine ⟨mem_closedBall_iff_norm.2 ?_, CircleFubini.foldH_mem_Hbar' w⟩
    rw [norm_foldH_sub_ofReal]
    exact (norm_sub_le_of_sphere (mem_sphere_iff_norm.1 hw)).trans hzs.le
  have hν0 : ν Kᶜ = 0 := mem_ae_iff.1 hνK
  have : IsProbabilityMeasure ν := by
    rw [hνdef, foldedCircle]; exact (Measure.isProbabilityMeasure_map_iff measurable_foldH.aemeasurable).2 inferInstance
  have hF := pull_stochFubini hW hD hr₁0 hD.hr₁ ν hν0 hYc hY
  have hbind : ν.bind (halfDiscPoisson b ρ) = halfDiscPoisson b ρ z :=
    bind_foldedCircle_halfDiscPoisson hρ hs (by linarith [hD.hr₁])
  have hν1 : ν Set.univ • halfDiscPoisson b ρ (b : ℂ) = halfDiscPoisson b ρ (b : ℂ) := by
    rw [measure_univ, one_smul]
  have hkz := hY (foldH z) (CircleFubini.foldH_mem_Hbar' z)
  have hzb : z ∈ ball (b : ℂ) ρ := mem_ball_iff_norm.2 (by linarith [hD.hr₁])
  have hfz : ‖foldH z - b‖ ≤ r₁ := by rw [norm_foldH_sub_ofReal]; linarith
  have hPf : halfDiscPoisson b ρ (foldH z) = halfDiscPoisson b ρ z := by
    unfold foldH; split_ifs
    · rfl
    · exact halfDiscPoisson_conj hρ hzb
  filter_upwards [hF, hkz] with ω h1 h2
  have hae : AEStronglyMeasurable (fun x => Y x ω) ν := by
    have hH : ∀ᵐ x ∂ν, x ∈ Hbar := hνK.mono fun x hx => hx.2
    rw [← Measure.restrict_eq_self_of_ae_mem hH]
    exact (hYc ω).aestronglyMeasurable isClosed_Hbar.measurableSet
  have e1 : ∫ w, Y (foldH w) ω ∂circleUnif z s = ∫ x, Y x ω ∂ν := by
    rw [hνdef, foldedCircle, integral_map measurable_foldH.aemeasurable hae]
  rw [e1, h1, show bal b ρ ν = ν.bind (halfDiscPoisson b ρ) from rfl, hbind, hν1, h2]
  simp only [pullIncr, retr_eq_self (CircleFubini.foldH_mem_Hbar' z) hfz, hPf]

theorem ae_harmonicOnNhd_pullY (hW : IsFreeGFFModConstH W P) (hD : PullData Φ b r₀ ρ r₁ m M)
    (hr₁0 : 0 < r₁) (hYc : ∀ ω, ContinuousOn (fun z => Y z ω) Hbar)
    (hY : ∀ z ∈ Hbar, Y z =ᵐ[P] pullIncr W Φ b ρ r₁ z) :
    ∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd (fun z => Y (foldH z) ω) (ball (b : ℂ) r₁) := by
  have hu : ∀ ω, Continuous fun z => Y (foldH z) ω := fun ω =>
    (hYc ω).comp_continuous CircleFubini.continuous_foldH' CircleFubini.foldH_mem_Hbar'
  set Q : (ℚ × ℚ) × ℚ → ℂ × ℝ :=
    Prod.map (Complex.equivRealProdCLM.symm ∘ Prod.map ((↑) : ℚ → ℝ) ((↑) : ℚ → ℝ))
      ((↑) : ℚ → ℝ) with hQ
  have hdense : DenseRange Q := by
    refine DenseRange.prodMap ?_ Rat.denseRange_cast
    exact (Complex.equivRealProdCLM.symm.surjective.denseRange).comp
      (Rat.denseRange_cast.prodMap Rat.denseRange_cast)
      Complex.equivRealProdCLM.symm.continuous
  set E : Set (ℂ × ℝ) := {p | 0 < p.2 ∧ ‖p.1 - b‖ + p.2 < r₁} with hE
  have hEo : IsOpen E := (isOpen_lt continuous_const continuous_snd).inter
    (isOpen_lt (((continuous_fst.sub continuous_const).norm).add continuous_snd) continuous_const)
  have hall : ∀ᵐ ω ∂P, ∀ q, Q q ∈ E →
      ∫ w, Y (foldH w) ω ∂circleUnif (Q q).1 (Q q).2 = Y (foldH (Q q).1) ω := by
    rw [ae_all_iff]
    intro q
    by_cases hq : Q q ∈ E
    · filter_upwards [ae_meanValue_pullY hW hD hr₁0 hYc hY hq.1 hq.2] with ω h _ using h
    · exact ae_of_all _ fun ω h => absurd h hq
  filter_upwards [hall] with ω hω
  refine harmonicOnNhd_of_meanValue (hu ω) isOpen_ball ?_
  have heq : Set.EqOn (fun p : ℂ × ℝ => ∫ w, Y (foldH w) ω ∂circleUnif p.1 p.2)
      (fun p => Y (foldH p.1) ω) E := by
    refine Set.EqOn.of_subset_closure (s := E ∩ Set.range Q) ?_
      (continuous_circleUnif_average (hu ω)).continuousOn
      ((hu ω).comp continuous_fst).continuousOn
      Set.inter_subset_left (hdense.open_subset_closure_inter hEo)
    rintro p ⟨hpE, q, rfl⟩
    exact hω q hpE
  intro z _ s hs hsub
  exact heq (x := (z, s)) ⟨hs, add_lt_of_closedBall_subset_ball hs hsub⟩

end

end G3Cv
end QuantumZipper
