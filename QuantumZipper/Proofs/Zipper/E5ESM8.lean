import QuantumZipper.Proofs.Zipper.E5ESM7
import QuantumZipper.Proofs.RS.TransienceCanon

/-!
# E5-ESM, part 8: supplying pathwise continuity `hBc` by a continuous version

Task E5-G0ESM (Theorem 1.3, node E5). The E-SM instance (`ESMInstUncond`) and hence
`e5_esm_model` (`E5ESM7`) need a Brownian motion with continuous paths at **every** `ω`, while
E5's setup (`E5.Setup`) only gives `IsBrownianReal B P` (a.s. continuity). Here:

* `lhsF_congr_ae`, `pmass_congr_ae`: E5's left side and the Palm mass depend on `B` only through
  its paths, `ω` by `ω` (checked definitionally by restricting to a one-point space), hence are
  unchanged when `B` is replaced by a version with the same paths a.s.;
* `e5_setup_version`: every E5 setup has a version `B''` with continuous paths at every `ω` which
  is again an E5 setup and has the same left side and Palm mass.

So `e5_esm_model` applies to every E5 setup through `B''`. Own bookkeeping; the version is
`RS.exists_good_version0`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace E5

open B2 E1

/-- The `ω`-integrand of E5's left side. -/
def lhsI {L : Type*} (loc : ℕ → FieldSample × (ℝ → ℝ) → L) (κ T : ℝ) {Ω : Type*}
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ϖ : Measure ℂ) (δ : ℝ) (R : ℕ) (C : ℝ)
    (Γ : L → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ x in Icc (-δ) 0,
    {x | realHitTime (Vr κ T B ω) x < ENNReal.ofReal T}.indicator
      (fun x => Γ (loc R (zcfg κ T B X ϖ C ω x))) x ∂nuPalm κ T B X ϖ ω

/-- The `ω`-integrand of the Palm mass. -/
def pmassI (κ T : ℝ) {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ϖ : Measure ℂ)
    (δ : ℝ) (ω : Ω) : ℝ≥0∞ :=
  nuPalm κ T B X ϖ ω {x | x ∈ Icc (-δ) 0 ∧ realHitTime (Vr κ T B ω) x < ENNReal.ofReal T}

lemma lhsI_congr {L : Type*} (loc : ℕ → FieldSample × (ℝ → ℝ) → L) (κ T : ℝ) {Ω : Type*}
    {B B' : ℝ≥0 → Ω → ℝ} (X : Ω → FieldSample) (ϖ : Measure ℂ) (δ : ℝ) (R : ℕ) (C : ℝ)
    (Γ : L → ℝ≥0∞) {ω : Ω} (h : ∀ t, B' t ω = B t ω) :
    lhsI loc κ T B' X ϖ δ R C Γ ω = lhsI loc κ T B X ϖ δ R C Γ ω := by
  have e1 : lhsI loc κ T B' X ϖ δ R C Γ ω =
      lhsI loc κ T (fun t (_ : Unit) => B' t ω) (fun _ => X ω) ϖ δ R C Γ () := rfl
  have e2 : lhsI loc κ T B X ϖ δ R C Γ ω =
      lhsI loc κ T (fun t (_ : Unit) => B t ω) (fun _ => X ω) ϖ δ R C Γ () := rfl
  have e3 : (fun t (_ : Unit) => B' t ω) = (fun t (_ : Unit) => B t ω) := by
    funext t _; exact h t
  rw [e1, e2, e3]

lemma pmassI_congr (κ T : ℝ) {Ω : Type*} {B B' : ℝ≥0 → Ω → ℝ} (X : Ω → FieldSample)
    (ϖ : Measure ℂ) (δ : ℝ) {ω : Ω} (h : ∀ t, B' t ω = B t ω) :
    pmassI κ T B' X ϖ δ ω = pmassI κ T B X ϖ δ ω := by
  have e1 : pmassI κ T B' X ϖ δ ω = pmassI κ T (fun t (_ : Unit) => B' t ω) (fun _ => X ω) ϖ δ () :=
    rfl
  have e2 : pmassI κ T B X ϖ δ ω = pmassI κ T (fun t (_ : Unit) => B t ω) (fun _ => X ω) ϖ δ () :=
    rfl
  have e3 : (fun t (_ : Unit) => B' t ω) = (fun t (_ : Unit) => B t ω) := by
    funext t _; exact h t
  rw [e1, e2, e3]

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {κ T : ℝ} {B B' : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {ϖ : Measure ℂ}

/-- E5's left side only sees the paths of `B`, a.s. -/
lemma lhsF_congr_ae {L : Type*} (loc : ℕ → FieldSample × (ℝ → ℝ) → L)
    (hae : ∀ᵐ ω ∂P, ∀ t, B' t ω = B t ω) (δ : ℝ) (R : ℕ) :
    lhsF loc κ T P B' X ϖ δ R = lhsF loc κ T P B X ϖ δ R := by
  funext C Γ
  exact lintegral_congr_ae (hae.mono fun _ h => lhsI_congr loc κ T X ϖ δ R C Γ h)

/-- The Palm mass only sees the paths of `B`, a.s. -/
lemma pmass_congr_ae (hae : ∀ᵐ ω ∂P, ∀ t, B' t ω = B t ω) (δ : ℝ) :
    pmass κ T P B' X ϖ δ = pmass κ T P B X ϖ δ :=
  lintegral_congr_ae (hae.mono fun _ h => pmassI_congr κ T X ϖ δ h)

/-- **Continuous version of an E5 setup.** -/
theorem e5_setup_version [IsProbabilityMeasure P] (hS : E5.Setup κ T P B X ϖ) :
    ∃ B'' : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous (B'' · ω)) ∧ E5.Setup κ T P B'' X ϖ ∧
      (∀ {L : Type*} (loc : ℕ → FieldSample × (ℝ → ℝ) → L) (δ : ℝ) (R : ℕ),
        lhsF loc κ T P B'' X ϖ δ R = lhsF loc κ T P B X ϖ δ R) ∧
      ∀ δ : ℝ, pmass κ T P B'' X ϖ δ = pmass κ T P B X ϖ δ := by
  obtain ⟨hκ, hκ4, hT, hB, hX, hind, hϖ⟩ := hS
  obtain ⟨B'', -, hc, -, hB'', hae⟩ := RS.exists_good_version0 hB
  have hpath : pathOf B'' =ᵐ[P] pathOf B := hae.mono fun ω h => funext h
  refine ⟨B'', hc, ⟨hκ, hκ4, hT, hB'', hX, hind.congr hpath.symm (ae_eq_refl _), hϖ⟩,
    fun loc δ R => lhsF_congr_ae loc hae δ R, fun δ => pmass_congr_ae hae δ⟩

end E5
end QuantumZipper
