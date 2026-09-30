import QuantumZipper.Proofs.Thm14.Wire

/-!
# THM14-WIRE (b): `WeldingDeterminationGraph` from Theorem 1.3 and two field-side inputs

Sheffield, *Conformal weldings of random surfaces* (arXiv:1012.4797), Theorem 1.4, last sentence
("In particular, `h` determines `η_T` almost surely", p. 16). The paper's argument: `h`
determines `ν_h`, hence `R = R_h`; `R` on `[0₋,0]` determines `η_T` (Theorem 1.4(a)); `η_T`
determines the driver. The formal version (`Proofs/Thm14/Determination.lean`) reduces
Theorem 1.4(b) to `WeldingDeterminationGraph`. Here we prove that proposition from

* Theorem 1.3 and `Blueprint.RohdeSchrammSimple` (through `Thm14Wire.theorem1_4a_of_theorem1_3_rss`,
  which uses the proved `RevMapCaratheodory`, `RevCouplingBoundaryMeasureRegular` and Option B
  removability; its first clause identifies `weldingHom W T` with `R_h` on `[0₋,0]`);
* the driver side `Thm14OptB.exists_measurable_driver_of_weldingData'` (the driver on `[0,T]` is
  a.s. a measurable function of the welding data `(0₋, weldingHom|ℚ∩[0₋,0])`);
* two **field-side inputs**, stated below as propositions (not yet proved):
  - `WeldRPairingReadable`: the rational values of `R_h` are a.s. a measurable function of
    countably many pairings of `h` with mass-zero test functions (the paper's "`h` determines
    `ν_h`", up to the constant factor that `R_h` does not see);
  - `ZeroMinusOfWeldR`: `0₋` is a.s. a measurable function of the rational values of `R_h`.
    The paper uses this silently: `R` is defined on all of `(−∞,0]`, and `0₋` is singled out by
    the capacity time `T` (the welded curve's half-plane capacity is strictly increasing in the
    welded interval `[x,0]`).

The combination is ours (a routine measurable-composition argument); no separate source.
-/

noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace QuantumZipper

namespace Thm14WDG

open Thm14Determination Thm14WeldingData

/-- **Field-side input 1**: `h` modulo additive constants determines `R_h` at rational points,
measurably and through countably many pairings with mass-zero test functions. -/
def WeldRPairingReadable : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ T : ℝ, 0 < T →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∃ (ρ : ℕ → TestFun0 H) (Ψ : (ℕ → ℝ) → (ℚ → ℝ)), Measurable Ψ ∧
      ∀ᵐ ω ∂P, Ψ (pairSeq ρ (couplingFieldRev κ (drive κ B ω) T (X ω))) =
        fun q : ℚ => weldR (Real.sqrt κ) (couplingFieldRev κ (drive κ B ω) T (X ω)) q

/-- **Field-side input 2**: `R_h` (at rational points) determines `0₋ = zeroMinus W T`,
measurably. -/
def ZeroMinusOfWeldR : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ T : ℝ, 0 < T →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∃ Z : (ℚ → ℝ) → ℝ, Measurable Z ∧
      ∀ᵐ ω ∂P, Z (fun q : ℚ => weldR (Real.sqrt κ) (couplingFieldRev κ (drive κ B ω) T (X ω)) q) =
        zeroMinus (drive κ B ω) T

/-- The welding data read off from `R` at rationals and a candidate `0₋ = Z R`. -/
def dataOf (Z : (ℚ → ℝ) → ℝ) (r : ℚ → ℝ) : ℝ × (ℚ → ℝ) :=
  (Z r, fun q => if Z r ≤ (q : ℝ) ∧ (q : ℝ) ≤ 0 then r q else 0)

theorem measurable_dataOf {Z : (ℚ → ℝ) → ℝ} (hZ : Measurable Z) : Measurable (dataOf Z) := by
  refine hZ.prodMk (measurable_pi_iff.2 fun q => ?_)
  refine Measurable.ite ?_ (measurable_pi_apply q) measurable_const
  exact (measurableSet_le hZ measurable_const).inter
    (MeasurableSet.const ((q : ℝ) ≤ 0))

/-- **`WeldingDeterminationGraph`** from Theorem 1.3, Rohde–Schramm simplicity and the two
field-side inputs. -/
theorem weldingDeterminationGraph_of (h13 : theorem1_3) (hRSS : Blueprint.RohdeSchrammSimple)
    (hR : WeldRPairingReadable) (hZ : ZeroMinusOfWeldR) : WeldingDeterminationGraph := by
  intro κ hκ0 hκ4 T hT Ω _ P _ B X hB hX hind
  obtain ⟨ρ, Ψ, hΨ, hΨae⟩ := hR κ hκ0 hκ4 T hT P B X hB hX hind
  obtain ⟨Z, hZm, hZae⟩ := hZ κ hκ0 hκ4 T hT P B X hB hX hind
  obtain ⟨F, hF, hFae⟩ := Thm14OptB.exists_measurable_driver_of_weldingData'
    CaraR.revMapCaratheodory hRSS hκ0 hκ4 hT P B hB
  have h14a := Thm14Wire.theorem1_4a_of_theorem1_3_rss h13 hRSS κ hκ0 hκ4 T hT P B X hB hX hind
  let g : (ℕ → ℝ) → (ℚ → ℝ) := fun p q => F (dataOf Z (Ψ p)) (max 0 (min (q : ℝ) T))
  have hg : Measurable g := measurable_pi_iff.2 fun q =>
    (measurable_pi_apply _).comp (hF.comp ((measurable_dataOf hZm).comp hΨ))
  refine ⟨ρ, {x | ∀ q : ℚ, x.2 q = g x.1 q}, ?_, ?_, ?_⟩
  · rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun q =>
      measurableSet_eq_fun ((measurable_pi_apply q).comp measurable_snd)
        ((measurable_pi_apply q).comp (hg.comp measurable_fst))
  · intro y z z' hz hz'
    exact funext fun q => (hz q).trans (hz' q).symm
  · filter_upwards [hΨae, hZae, hFae, h14a] with ω hΨω hZω hFω h14ω
    have hdata : dataOf Z (Ψ (pairSeq ρ (couplingFieldRev κ (drive κ B ω) T (X ω)))) =
        weldingData (drive κ B ω) T := by
      rw [hΨω]
      unfold dataOf weldingData
      rw [hZω]
      refine Prod.ext rfl (funext fun q => ?_)
      simp only
      split_ifs with hq
      · exact (h14ω.1.2 q hq).symm
      · rfl
    intro q
    change drive κ B ω (max 0 (min (q : ℝ) T)) = F (dataOf Z (Ψ _)) (max 0 (min (q : ℝ) T))
    rw [hdata]
    exact (hFω _ ⟨le_max_left _ _, max_le hT.le (min_le_right _ _)⟩).symm

/-- **Theorem 1.4(b)** from Theorem 1.3, Rohde–Schramm simplicity and the two field-side
inputs. -/
theorem theorem1_4b_of_theorem1_3_rss (h13 : theorem1_3) (hRSS : Blueprint.RohdeSchrammSimple)
    (hR : WeldRPairingReadable) (hZ : ZeroMinusOfWeldR) : theorem1_4b :=
  theorem1_4b_of_weldingDeterminationGraph (weldingDeterminationGraph_of h13 hRSS hR hZ)

end Thm14WDG

end QuantumZipper
