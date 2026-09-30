import QuantumZipper.Proofs.Thm18.G3SchemeGFF
import QuantumZipper.Proofs.Zipper.D3PlusN1Model
import QuantumZipper.Proofs.LQG.WedgeToolkit
import QuantumZipper.Statements.CouplingFields

/-!
# G3 concrete scheme (part 1): the region fields and their exact measurability (M1, fields)

Sheffield, arXiv:1012.4797, proof of Theorem 1.8 (§5.4, pp. 70–71): the two zooms are built from
the field restricted to two disjoint half-discs, and the GFF Markov property makes them
conditionally independent given the field outside. Here the field is Theorem 1.2's
`h = 𝔥₀ + X − X(unit semicircle)` (`normField`, read on probability measures), and the *region
field* of a half-disc `B(t, r) ∩ ℍ` is `h` restricted to the folded circles carried by a closed
sub-disc of `B(t, r)` (`circIn t r`), junk `0` at every other measure (`restrictField`). The
*gap field* is `h` restricted to the folded circles giving no mass to either open disc
(`circOut`).

On `circIn t r` the identity `h(μ) = 𝔥₀(μ) + markovZ(μ) + (X(bal μ) − X(S))` holds for **every**
`ω` (it is the definition of `markovZ`), so each coordinate of the region field is exactly
measurable for `localSigma ⊔ outsideSigma2` (`measurable_regionField`); the gap field is exactly
`outsideSigma2`-measurable (`measurable_gapField`). No null-set modification is needed. The
pattern is that of `D3Plus.macroF` (`D3PlusN1Model.lean`). Own elementary arguments (AGENT_GUIDE
cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set MeasurableSpace
open scoped ENNReal

namespace QuantumZipper
namespace Thm18Asm

open K3

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {X : Ω → FieldSample}

/-- The reference measure of the normalization `h₁(0) = 0`: the unit folded semicircle. -/
abbrev refS : Measure ℂ := foldedCircle 0 1

/-- Theorem 1.2's field `h = 𝔥₀ + X − X(S)` (`𝔥₀ = h0rev (γ²) = (2/γ) log|·|`), read on
probability measures (the only measures at which the scheme reads it). -/
def normField (γ : ℝ) (X : Ω → FieldSample) (ω : Ω) : FieldSample :=
  fun μ => ofFun (h0rev (γ ^ 2)) μ + (X ω μ - X ω refS)

/-- Folded circles carried by a closed sub-disc of `B(t, r)`. -/
def circIn (t r : ℝ) : Set (Measure ℂ) :=
  {μ | ∃ (d : ℂ) (ρ : ℝ), 0 < ρ ∧ μ = foldedCircle d ρ ∧
    ∃ r' < r, μ (closedBall (t : ℂ) r')ᶜ = 0}

/-- Folded circles giving no mass to either of two open discs. -/
def circOut (t₁ r₁ t₂ r₂ : ℝ) : Set (Measure ℂ) :=
  {μ | ∃ (d : ℂ) (ρ : ℝ), 0 < ρ ∧ μ = foldedCircle d ρ ∧
    μ (ball (t₁ : ℂ) r₁ ∪ ball (t₂ : ℂ) r₂) = 0}

open Classical in
/-- The field `y` read only on the measures of `A` (junk `0` elsewhere). -/
def restrictField (A : Set (Measure ℂ)) (y : FieldSample) : FieldSample :=
  fun μ => if μ ∈ A then y μ else 0

/-- The region field of the half-disc `B(t, r) ∩ ℍ`. -/
def regionField (γ t r : ℝ) (X : Ω → FieldSample) (ω : Ω) : FieldSample :=
  restrictField (circIn t r) (normField γ X ω)

/-- The gap field (outside both half-discs). -/
def gapField (γ t₁ r₁ t₂ r₂ : ℝ) (X : Ω → FieldSample) (ω : Ω) : FieldSample :=
  restrictField (circOut t₁ r₁ t₂ r₂) (normField γ X ω)

theorem isLocalH_of_mem_circIn {t r : ℝ} {μ : Measure ℂ} (h : μ ∈ circIn t r) :
    IsLocalH t r μ := by
  obtain ⟨d, ρ, hρ, rfl, r', hr', hμ⟩ := h
  exact ⟨D3Plus.isAdmissibleH_foldedCircle' d hρ, r', hr', hμ⟩

omit mΩ in
theorem measurable_markovZ_localSigma {t r : ℝ} {μ : Measure ℂ} (hμ : IsLocalH t r μ) :
    Measurable[localSigma X t r] fun ω => markovZ X t r ω μ :=
  measurable_iff_comap_le.2 (le_iSup (fun μ : {μ // IsLocalH t r μ} =>
    MeasurableSpace.comap (fun ω => markovZ X t r ω μ.1) inferInstance) ⟨μ, hμ⟩)

/-- The unit semicircle misses every disc inside the unit disc. -/
theorem refS_ball_null {t r : ℝ} (h : |t| + r ≤ 1) : refS (ball (t : ℂ) r) = 0 := by
  refine measure_mono_null (fun x hx => ?_) (ae_iff.1 (WedgeTK.fc_ae_norm one_pos))
  show ¬ ‖x‖ = 1
  intro hx1
  have h1 : ‖x - t‖ < r := mem_ball_iff_norm.1 hx
  have h2 : ‖x‖ ≤ ‖x - t‖ + ‖(t : ℂ)‖ := by
    calc ‖x‖ = ‖(x - t) + t‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
  have h3 : ‖(t : ℂ)‖ = |t| := by simp
  linarith

theorem refS_union_null {t₁ r₁ t₂ r₂ : ℝ} (h₁ : |t₁| + r₁ ≤ 1) (h₂ : |t₂| + r₂ ≤ 1) :
    refS (ball (t₁ : ℂ) r₁ ∪ ball (t₂ : ℂ) r₂) = 0 :=
  measure_union_null (refS_ball_null h₁) (refS_ball_null h₂)

/-- **M1 (region field).** The region field of `B(t, r)` is exactly measurable for the local
part of the field in `B(t, r)` and the field outside both discs, provided the half-disc Poisson
kernels of `B(t, r)` charge neither disc. -/
theorem measurable_regionField (γ : ℝ) {t₁ r₁ t₂ r₂ t r : ℝ} (hr : 0 < r)
    (hbal : ∀ z, halfDiscPoisson t r z (ball (t₁ : ℂ) r₁ ∪ ball (t₂ : ℂ) r₂) = 0)
    (hS : refS (ball (t₁ : ℂ) r₁ ∪ ball (t₂ : ℂ) r₂) = 0) :
    Measurable[localSigma X t r ⊔ outsideSigma2 X t₁ r₁ t₂ r₂] (regionField γ t r X) := by
  classical
  refine @D3Plus.measurable_fieldSample_of Ω (localSigma X t r ⊔ outsideSigma2 X t₁ r₁ t₂ r₂)
    _ fun μ => ?_
  by_cases h : μ ∈ circIn t r
  · have hloc := isLocalH_of_mem_circIn h
    obtain ⟨d, ρ, hρ, rfl, r', hr', hμr⟩ := h
    simp only [regionField, restrictField, if_pos (show foldedCircle d ρ ∈ circIn t r from
      ⟨d, ρ, hρ, rfl, r', hr', hμr⟩)]
    have e : (fun ω => normField γ X ω (foldedCircle d ρ)) = fun ω =>
        ofFun (h0rev (γ ^ 2)) (foldedCircle d ρ) + (markovZ X t r ω (foldedCircle d ρ) +
          (X ω (bal t r (foldedCircle d ρ)) - X ω refS)) := by
      funext ω; simp only [normField, markovZ]; ring
    rw [e]
    have hm : bal t r (foldedCircle d ρ) univ = refS univ := by
      rw [bal_univ hr hr' hμr, measure_univ, measure_univ]
    have hout : Measurable[outsideSigma2 X t₁ r₁ t₂ r₂]
        fun ω => X ω (bal t r (foldedCircle d ρ)) - X ω refS :=
      measurable_outsideSigma2 (isAdmissibleH_bal hr hr' hμr)
        (D3Plus.isAdmissibleH_foldedCircle' 0 one_pos) hm
        (bal_null_of_forall (measurableSet_ball.union measurableSet_ball) hbal) hS
    exact measurable_const.add (((measurable_markovZ_localSigma hloc).mono le_sup_left le_rfl).add
      (hout.mono le_sup_right le_rfl))
  · simp only [regionField, restrictField, if_neg h]
    exact measurable_const

/-- **M1 (gap field).** The gap field is exactly `outsideSigma2`-measurable. -/
theorem measurable_gapField (γ : ℝ) {t₁ r₁ t₂ r₂ : ℝ}
    (hS : refS (ball (t₁ : ℂ) r₁ ∪ ball (t₂ : ℂ) r₂) = 0) :
    Measurable[outsideSigma2 X t₁ r₁ t₂ r₂] (gapField γ t₁ r₁ t₂ r₂ X) := by
  classical
  refine @D3Plus.measurable_fieldSample_of Ω (outsideSigma2 X t₁ r₁ t₂ r₂) _ fun μ => ?_
  by_cases h : μ ∈ circOut t₁ r₁ t₂ r₂
  · simp only [gapField, restrictField, if_pos h]
    obtain ⟨d, ρ, hρ, rfl, hμ0⟩ := h
    have hm : foldedCircle d ρ univ = refS univ := by rw [measure_univ, measure_univ]
    exact measurable_const.add (measurable_outsideSigma2 (D3Plus.isAdmissibleH_foldedCircle' d hρ)
      (D3Plus.isAdmissibleH_foldedCircle' 0 one_pos) hm hμ0 hS)
  · simp only [gapField, restrictField, if_neg h]
    exact measurable_const

/-- The Poisson kernels of the first disc charge neither disc. -/
theorem halfDiscPoisson_union_null₁ {t₁ r₁ t₂ r₂ : ℝ} (hr₁ : 0 < r₁)
    (hd : r₁ + r₂ ≤ dist (t₁ : ℂ) t₂) (z : ℂ) :
    halfDiscPoisson t₁ r₁ z (ball (t₁ : ℂ) r₁ ∪ ball (t₂ : ℂ) r₂) = 0 :=
  measure_union_null (halfDiscPoisson_ball hr₁ z)
    (halfDiscPoisson_ball_other (t₁ := t₂) (r₁ := r₂) hr₁
      (by rw [dist_comm, add_comm]; exact hd) z)

/-- The Poisson kernels of the second disc charge neither disc. -/
theorem halfDiscPoisson_union_null₂ {t₁ r₁ t₂ r₂ : ℝ} (hr₂ : 0 < r₂)
    (hd : r₁ + r₂ ≤ dist (t₁ : ℂ) t₂) (z : ℂ) :
    halfDiscPoisson t₂ r₂ z (ball (t₁ : ℂ) r₁ ∪ ball (t₂ : ℂ) r₂) = 0 :=
  measure_union_null (halfDiscPoisson_ball_other hr₂ hd z) (halfDiscPoisson_ball hr₂ z)

/-! ## Transport to the Palm space `Ω × E` -/

omit mΩ in
/-- A function of `ω` measurable for a region's local part and the outside field is measurable,
on `Ω × E`, for the region's σ-algebra used by `condIndepCE_twoHalfDisc_palm`. -/
theorem measurable_comp_fst_palm {E : Type*} [MeasurableSpace E] {t r t₁ r₁ t₂ r₂ : ℝ}
    {β : Type*} [MeasurableSpace β] {f : Ω → β}
    (hf : Measurable[localSigma X t r ⊔ outsideSigma2 X t₁ r₁ t₂ r₂] f) :
    Measurable[(localSigma X t r).comap Prod.fst ⊔ outsideSigmaPalm E X t₁ r₁ t₂ r₂]
      fun p : Ω × E => f p.1 := by
  refine measurable_iff_comap_le.2 ?_
  show MeasurableSpace.comap (f ∘ Prod.fst) _ ≤ _
  rw [← MeasurableSpace.comap_comp]
  refine (MeasurableSpace.comap_mono (measurable_iff_comap_le.1 hf)).trans ?_
  rw [MeasurableSpace.comap_sup]
  exact sup_le_sup_left le_sup_left _

omit mΩ in
theorem measurable_snd_palm {E : Type*} [MeasurableSpace E] {t r t₁ r₁ t₂ r₂ : ℝ} :
    Measurable[(localSigma X t r).comap Prod.fst ⊔ outsideSigmaPalm E X t₁ r₁ t₂ r₂]
      fun p : Ω × E => p.2 :=
  measurable_iff_comap_le.2 (le_sup_right.trans le_sup_right)

end Thm18Asm
end QuantumZipper
