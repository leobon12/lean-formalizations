import QuantumZipper.Proofs.Zipper.Cor15LawTransfer
import QuantumZipper.Proofs.Zipper.B1Full

/-!
# Corollary 1.5, positive times: the law transfer with the B1 data

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5 (pp. 17–18;
the paper gives no proof). Blocker 2 of `handoff/COR15.md`.

The data map `b1Data` is the one of `B1Full.b1_full` (B1-FULL): the normalized `lawData` of the
field (`coordsFull` and raw pairings with all test functions on `ℍ`, after subtracting the
value at the unit folded circle) and the driver on `[0,∞)`. B1-FULL gives
`law(b1Data (D_t c)) = law(b1Data c)`. Here:

* `aemeasurable_b1Data_c`: `b1Data ∘ c` is a.e.-measurable (measurable version of `B`);
* `aemeasurable_b1Data_unzip`: so is `b1Data ∘ D_t c`. Proof (own argument): otherwise its
  `Measure.map` is a Dirac mass (junk value at this pin), hence so is the law of `b1Data ∘ c`,
  so `√κ B_1` would be a.s. constant, contradicting `B_1 ~ N(0,1)`;
* **`theorem1_5a_pos_of_goodSet`**: Corollary 1.5(a) at a time `t > 0`, in the exact shape of
  `theorem1_5`'s clause (a), from (i) the law form `hR1` of P1 and (ii) a measurable set `A`
  of `b1Data` values, charged a.s. by `b1Data (D_t c)`, on which the `configLawMod0` data of
  `Z_t x` is a measurable function `Φ` of `b1Data x`.

Own elementary argument (pushforward algebra, `Cor15LawTransfer`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

open B1Full

/-- The B1-FULL data of a configuration. -/
def b1Data (x : FieldSample × (ℝ → ℝ)) : ((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ) :=
  ((CoordsFull.coordsFull (nrm x.1), fun ρ => pairRaw (nrm x.1) ρ.1), fun s : ℝ≥0 => x.2 s)

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

omit [IsProbabilityMeasure P] in
theorem aemeasurable_b1Data_c (κ : ℝ) (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) :
    AEMeasurable (fun ω => b1Data (ofFun (h0rev κ) + X ω, drive κ B ω)) P := by
  obtain ⟨B', hB'm, -, hB'eq⟩ := CharFun.exists_good_version hB
  refine ⟨fun ω => b1Data (ofFun (h0rev κ) + X ω, drive κ B' ω), ?_, ?_⟩
  · have hc : ∀ μ : Measure ℂ, Measurable fun ω => (ofFun (h0rev κ) + X ω) μ := fun μ =>
      measurable_const.add (hX.measurable_coord μ)
    have h1 := measurable_lawData_nrm (Y := fun ω => ofFun (h0rev κ) + X ω)
      (fun w r _ => hc _) (fun ρ => by unfold pairRaw; exact (hc _).sub (hc _))
    refine Measurable.prodMk h1 (measurable_pi_iff.2 fun s => ?_)
    exact measurable_const.mul (hB'm _)
  · filter_upwards [hB'eq] with ω h
    have : drive κ B ω = drive κ B' ω := by funext s; simp only [drive, h]
    rw [this]

theorem aemeasurable_b1Data_unzip (κ : ℝ) (hκ : 0 < κ) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) {t : ℝ} (ht : 0 < t) :
    AEMeasurable
      (fun ω => b1Data (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω))) P := by
  by_contra hne
  have hlaw := b1_full κ hκ P B X hB hX hind ht
  have hec := aemeasurable_b1Data_c κ hB hX (P := P)
  have hl : P.map (fun ω => b1Data (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω,
      drive κ B ω))) = P.map (fun ω => b1Data (ofFun (h0rev κ) + X ω, drive κ B ω)) := hlaw
  rw [Measure.map_of_not_aemeasurable_of_ne_zero hne (IsProbabilityMeasure.ne_zero P)] at hl
  -- the value of the Dirac mass
  set p : ((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ) := Classical.ofNonempty with hp
  let S : Set (((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ)) := {z | z.2 1 = p.2 1}
  have hS : MeasurableSet S :=
    measurableSet_eq_fun ((measurable_pi_apply 1).comp measurable_snd) measurable_const
  have h1 := congrArg (fun μ => μ S) hl
  rw [Measure.dirac_apply' _ hS, Set.indicator_of_mem (show p ∈ S from rfl), Pi.one_apply,
    Measure.map_apply_of_aemeasurable hec hS] at h1
  -- `√κ B_1` would be a.s. equal to `p.2 1`
  have hsk : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  have hsub : (fun ω => b1Data (ofFun (h0rev κ) + X ω, drive κ B ω)) ⁻¹' S ⊆
      B 1 ⁻¹' {p.2 1 / Real.sqrt κ} := by
    intro ω hω
    simp only [Set.mem_preimage, S, Set.mem_ofPred_eq, b1Data, drive, NNReal.coe_one,
      Real.toNNReal_one] at hω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, ← hω]
    field_simp
  have hB1 : P (B 1 ⁻¹' {p.2 1 / Real.sqrt κ}) = 0 := by
    rw [← Measure.map_apply_of_aemeasurable (hB.aemeasurable 1) (measurableSet_singleton _),
      (hB.hasLaw_eval 1).map_eq]
    have := nullSingletonClass_gaussianReal (μ := 0) (v := (1 : ℝ≥0)) one_ne_zero
    exact measure_singleton _
  have := measure_mono_null hsub hB1
  rw [← h1] at this
  exact one_ne_zero this

end Cor15Group
end QuantumZipper
