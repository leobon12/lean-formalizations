import QuantumZipper.Proofs.Zipper.Cor15GoodMarg

/-!
# Corollary 1.5(a), positive times: good sets one coordinate at a time

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5 (pp. 17–18;
the paper gives no proof). Task COR15-R12.

The per-marginal input `hgood` of `theorem1_5a_pos_of_goodSets` follows from good sets for one
coordinate of `mod0Data (Z_t x)` at a time (finite intersections of good sets):

* `hgood_of_coords`: `hgood` from per-coordinate good sets (abstract);
* `drvGood_of_weldRead`: the per-coordinate good sets for the driver coordinates of `Z_t x`
  follow from a measurable reading `F` of the welding driver on `[0,t]` from `b1Data`
  (`Cor15WeldReadStmt`);
* **`theorem1_5a_pos_of_coords`**: Corollary 1.5(a) at `t > 0`, `κ ∈ (0,4)`, from Theorem 1.3,
  `RohdeSchrammSimple`, and the inputs `hZc`, `hZy` (a.e.-measurability), `hraw` (R1,
  per test function), `hF` (`Cor15WeldReadStmt`), `hpair` (per test function: the zipped raw
  pairing is a measurable function of `b1Data` on a good set).

Own elementary argument.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

section Abstract

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E : Type*} [MeasurableSpace E]

/-- **Per-marginal good sets from per-coordinate good sets.** -/
theorem hgood_of_coords {Z : FieldSample × (ℝ → ℝ) → FieldSample × (ℝ → ℝ)}
    {e : FieldSample × (ℝ → ℝ) → E} {y : Ω → FieldSample × (ℝ → ℝ)}
    (hpair : ∀ ρ : TestFun0 H, ∃ Φ : E → ℝ, Measurable Φ ∧ ∃ A : Set E, MeasurableSet A ∧
      (∀ x, e x ∈ A → (mod0Data (Z x)).1 ρ = Φ (e x)) ∧ ∀ᵐ ω ∂P, e (y ω) ∈ A)
    (hdrv : ∀ s : ℝ≥0, ∃ Φ : E → ℝ, Measurable Φ ∧ ∃ A : Set E, MeasurableSet A ∧
      (∀ x, e x ∈ A → (mod0Data (Z x)).2 s = Φ (e x)) ∧ ∀ᵐ ω ∂P, e (y ω) ∈ A)
    (J : Finset (TestFun0 H)) (S : Finset ℝ≥0) :
    ∃ Φ : E → (J → ℝ) × (S → ℝ), Measurable Φ ∧ ∃ A : Set E, MeasurableSet A ∧
      (∀ x, e x ∈ A → margJS J S (mod0Data (Z x)) = Φ (e x)) ∧ ∀ᵐ ω ∂P, e (y ω) ∈ A := by
  choose Φp hΦp Ap hAp hfp hyp using hpair
  choose Φd hΦd Ad hAd hfd hyd using hdrv
  refine ⟨fun z => (fun ρ : J => Φp ρ z, fun s : S => Φd s z), ?_,
    (⋂ ρ : J, Ap ρ) ∩ ⋂ s : S, Ad s, ?_, ?_, ?_⟩
  · exact (measurable_pi_iff.2 fun ρ : J => hΦp ρ.1).prodMk
      (measurable_pi_iff.2 fun s : S => hΦd s.1)
  · exact (MeasurableSet.iInter fun ρ : J => hAp ρ.1).inter
      (MeasurableSet.iInter fun s : S => hAd s.1)
  · intro x hx
    simp only [mem_inter_iff, mem_iInter] at hx
    refine Prod.ext (funext fun ρ => ?_) (funext fun s => ?_)
    · exact hfp ρ x (hx.1 ρ)
    · exact hfd s x (hx.2 s)
  · have h1 : ∀ᵐ ω ∂P, ∀ ρ : J, e (y ω) ∈ Ap ρ := ae_all_iff.2 fun ρ => hyp ρ
    have h2 : ∀ᵐ ω ∂P, ∀ s : S, e (y ω) ∈ Ad s := ae_all_iff.2 fun s => hyd s
    filter_upwards [h1, h2] with ω h₁ h₂
    simp only [mem_inter_iff, mem_iInter]
    exact ⟨h₁, h₂⟩

end Abstract

section Thm

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- **Measurable reading of the welding driver from `b1Data`, on a good set** (remaining input):
a measurable `F` from `b1Data` values to drivers and a measurable set `A` of `b1Data` values,
charged a.s. by `b1Data (D_t c)`, such that for every configuration `x` with `b1Data x ∈ A`,
`weldDriver √κ x.1 t = F (b1Data x)` on `[0,t]`. -/
def Cor15WeldReadStmt (κ t : ℝ) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) : Prop :=
  ∃ F : ((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ) → ℝ → ℝ, Measurable F ∧
    ∃ A : Set (((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ)), MeasurableSet A ∧
      (∀ x, b1Data x ∈ A → EqOn (weldDriver (Real.sqrt κ) x.1 t) (F (b1Data x)) (Icc 0 t)) ∧
      ∀ᵐ ω ∂P, b1Data (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)) ∈ A

/-- **Pairing coordinates of `Z_t x`, one test function at a time** (remaining input). -/
def Cor15PairReadStmt (κ t : ℝ) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) : Prop :=
  ∀ ρ : TestFun0 H, ∃ Φ : ((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ) → ℝ, Measurable Φ ∧
    ∃ A : Set (((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ)), MeasurableSet A ∧
      (∀ x, b1Data x ∈ A → (mod0Data (zipCapUp (Real.sqrt κ) t x)).1 ρ = Φ (b1Data x)) ∧
      ∀ᵐ ω ∂P, b1Data (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)) ∈ A

omit [IsProbabilityMeasure P] in
/-- The driver coordinates of `Z_t x` from a measurable reading of the welding driver. -/
theorem drvGood_of_weldRead {κ t : ℝ} (ht : 0 ≤ t) (hF : Cor15WeldReadStmt κ t P B X)
    (s : ℝ≥0) :
    ∃ Φ : ((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ) → ℝ, Measurable Φ ∧
      ∃ A : Set (((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ)), MeasurableSet A ∧
      (∀ x, b1Data x ∈ A → (mod0Data (zipCapUp (Real.sqrt κ) t x)).2 s = Φ (b1Data x)) ∧
      ∀ᵐ ω ∂P, b1Data (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)) ∈ A := by
  obtain ⟨F, hFm, A, hA, hEq, hyA⟩ := hF
  have hev : ∀ r : ℝ, Measurable fun z : ((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ) => F z r :=
    fun r => (measurable_pi_apply r).comp hFm
  refine ⟨fun z => if (s : ℝ) ≤ t then F z (t - s) - F z t
      else z.2 (Real.toNNReal ((s : ℝ) - t)) - F z t, ?_, A, hA, fun x hx => ?_, hyA⟩
  · by_cases hs : (s : ℝ) ≤ t
    · simp only [hs, ↓reduceIte]; exact (hev _).sub (hev _)
    · simp only [hs, ↓reduceIte]
      exact ((measurable_pi_apply _).comp measurable_snd).sub (hev _)
  · have hW := hEq x hx
    have htt : t ∈ Icc (0 : ℝ) t := ⟨ht, le_rfl⟩
    show (if (s : ℝ) ≤ t then _ else _) = _
    simp only [max_eq_left (NNReal.coe_nonneg s)]
    by_cases hs : (s : ℝ) ≤ t
    · simp only [hs, ↓reduceIte]
      rw [hW htt, hW ⟨sub_nonneg.2 hs, sub_le_self _ s.2⟩]
    · simp only [hs, ↓reduceIte]
      rw [hW htt]
      simp only [b1Data, Real.coe_toNNReal _ (sub_nonneg.2 (not_le.1 hs).le)]

/-- **Corollary 1.5(a) at `t > 0`, per-coordinate form** (clause (a) of `theorem1_5`, for
`κ ∈ (0,4)`): from Theorem 1.3, `RohdeSchrammSimple`, a.e.-measurability of the zipped data
(`hZc`, `hZy`), the per-test-function form `hraw` of P1, the measurable driver reading `hF`, and
the per-test-function pairing reading `hpair`. -/
theorem theorem1_5a_pos_of_coords (h13 : theorem1_3) (hRSS : Blueprint.RohdeSchrammSimple)
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) {t : ℝ} (ht : 0 < t)
    (hZc : AEMeasurable (fun ω => mod0Data (zipCapUp (Real.sqrt κ) t
      (ofFun (h0rev κ) + X ω, drive κ B ω))) P)
    (hZy : AEMeasurable (fun ω => mod0Data (zipCapUp (Real.sqrt κ) t
      (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)))) P)
    (hraw : ∀ ρ : TestFun0 H, ∀ᵐ ω ∂P,
      pairRaw (zipCapUp (Real.sqrt κ) t
        (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω))).1 ρ.1.1 =
      pairRaw (ofFun (h0rev κ) + X ω) ρ.1.1)
    (hF : Cor15WeldReadStmt κ t P B X) (hpair : Cor15PairReadStmt κ t P B X) :
    configLawMod0 (fun ω => zipCap (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)) P =
      configLawMod0 (fun ω => (ofFun (h0rev κ) + X ω, drive κ B ω)) P :=
  theorem1_5a_pos_of_perTest h13 hRSS hκ hκ4 hB hX hind ht hZc hZy hraw
    (hgood_of_coords hpair (drvGood_of_weldRead ht.le hF))

end Thm

end Cor15Group
end QuantumZipper
