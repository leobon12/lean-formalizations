/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1ELawSample
import InteractingSLE.Spec.ZhanGT4.A1RLawEightRect

/-!
# Zhan's A.1 under R83, (Eight), small-curve direction: the per-sample frozen law

Packet PROVE-A1-EIGHTLAW (R83). The image curve is the small curve (on `X`, parameter `κ̂ = kh κ`), the conditioning
curve the large curve (on `Y`), frozen at the height `σ`. For regular Eight marginals with continuous Brownian paths at
every sample and a `GoodSmallEight` small curve at every sample (the patched marginals):

* **`eightChargeEquiv`**, `imageCharge_eight_left`, `imageCharge_eight_right`: the image charges of the Eight records
  in the order of the small image word (`smallEightRhoL κ`, `smallEightRhoR κ`);
* **`eight_isSourceColumn`**: at every frozen sample `y₀` and every height `σ ∈ (0, S₂ᵐ(y₀)]` the Eight records of the
  cofinal protected pair `m` form a seed source column (`IsSourceColumn`);
* **`eight_isSeedSampleLaw`**: under the rectangle density `P₁.withDensity (x ↦ M(S₁ᵐ(x), σ))` (A1-RECTLAW2's
  small-curve family density at a protected frozen time), every image datum equal up to the cap to the seeded capacity
  coordinates of the column (driver, the three image forces in the small image word's order, the residual as the
  noise, the cap the capacity horizon, the other caps image capacities at own-time stopping times) satisfies
  `IsSeedSampleLaw`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1ELaw

open QuantumZipper (H fwdMap fwdHull)
open A2X A1Ref A1Canon A1Core A1Frozen A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin
  A1Asm A1Family Girsanov A1RLaw

/-! ### The charge enumeration of the small Eight image word -/

/-- **The image charges of the Eight records in the order of the small image word**: the left seed `x⁻` (mark `0`,
index `1`), then on the right the seed `x⁺` (mark `1`, index `2`) and the other source (the large curve's tip,
index `0`). -/
def eightChargeEquiv : Fin 1 ⊕ Fin 2 ≃ Fin (2 + 1) where
  toFun := Sum.elim (fun _ => 1) ![2, 0]
  invFun := ![Sum.inr 1, Sum.inl 0, Sum.inr 0]
  left_inv := by
    intro i
    rcases i with i | i <;> fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem imageCharge_eight_left {κ : ℝ} (hκ : κ ≠ 0) {s : SeedData 2} (hsκ : s.κ = kh κ) (hsr : s.r = eightRR κ)
    (i : Fin 1) : s.imageCharge (eightChargeEquiv (.inl i)) = smallEightRhoL κ i := by
  have hk : kh κ ≠ 0 := by unfold kh; exact div_ne_zero (by norm_num) hκ
  fin_cases i
  simp only [eightChargeEquiv, Equiv.coe_fn_mk, Sum.elim_inl, SeedData.imageCharge, hsκ, hsr]
  show kh κ * eightRR κ 0 = smallEightRhoL κ 0
  simp only [eightRR, Matrix.cons_val_zero]
  field_simp

theorem imageCharge_eight_right {κ : ℝ} (hκ : κ ≠ 0) {s : SeedData 2} (hsκ : s.κ = kh κ) (hsr : s.r = eightRR κ)
    (j : Fin 2) : s.imageCharge (eightChargeEquiv (.inr j)) = smallEightRhoR κ j := by
  have hk : kh κ ≠ 0 := by unfold kh; exact div_ne_zero (by norm_num) hκ
  fin_cases j
  · simp only [eightChargeEquiv, Equiv.coe_fn_mk, Sum.elim_inr, SeedData.imageCharge, hsκ, hsr]
    show kh κ * eightRR κ 1 = smallEightRhoR κ 0
    simp only [eightRR, Matrix.cons_val_one, Matrix.cons_val_zero]
    field_simp
  · simp only [eightChargeEquiv, Equiv.coe_fn_mk, Sum.elim_inr, SeedData.imageCharge, hsκ]
    show -(kh κ / 2) = smallEightRhoR κ 1
    simp only [smallEightRhoR, Matrix.cons_val_one, Matrix.cons_val_zero]

/-! ### The source column at every frozen height -/

section Column

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- The column of (Eight) records at the frozen sample `y₀` and height `σ` (rectangle `m`). -/
abbrev eightCol (κ x : ℝ) (W₁ : ℝ≥0 → X → ℝ) (VL₁ : Fin 1 → ℝ≥0 → X → ℝ) (VR₁ : Fin 2 → ℝ≥0 → X → ℝ)
    (ζ₁ : X → ℝ≥0∞) (W₂ : ℝ≥0 → Y → ℝ) (m : ℕ) (σ : ℝ) (y₀ : Y) : X → SeedData 2 :=
  fun ω => eightRec κ (-x) W₁ VL₁ VR₁ W₂ (eightS₁ x W₁ ζ₁) m σ (ω, y₀)

/-- **The Eight records at a frozen height form a seed source column**: for regular Eight marginals with continuous
Brownian paths at every sample and a `GoodSmallEight` small curve at every sample, at every frozen sample `y₀` and every
height `σ ∈ (0, S₂ᵐ(y₀)]`, the records `x ↦ eightRec κ (−x) … m σ (x, y₀)` of the cofinal protected pair `m` form an
`IsSourceColumn`, and the pair is protected. -/
theorem eight_isSourceColumn {κ x : ℝ} (hκ8 : 8 ≤ κ) (hx : x < 0) {P₁ : Measure X} {𝓖₁ : Filtration ℝ≥0 mX}
    [𝓖₁.IsRightContinuous] {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ}
    {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ}
    {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞} {P₂ : Measure Y} {𝓖₂ : Filtration ℝ≥0 mY}
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))
    (m : ℕ) (y₀ : Y) {σ : ℝ} (hσ : 0 < σ) (hσS : σ ≤ eightS₂ x W₂ ζ₂ m y₀) :
    IsProtectedPair (cofH₁ (-x) ![] m) (cofH₂ (-x) ![] m) (cofδ (-x) ![] m) (-x) (cofq (-x) ![] m)
        (cofd (-x) ![] m) ∧
      IsSourceColumn (cofH₁ (-x) ![] m) (cofH₂ (-x) ![] m) (-x) (cofTm (-x) ![] m) (kh κ) (eightRR κ) 𝓖₁ P₁ σ
        (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ m σ y₀) (eightS₁ x W₁ ζ₁ m) := by
  have hx₂ : 0 < -x := by linarith
  have hne : (goodIdx (-x) (![] : Fin 0 → ℝ)).Nonempty :=
    goodIdx_nonempty hx₂ (fun m => m.elim0) (fun m => m.elim0)
  have hF := isEnclFamily_cof hne
  obtain ⟨-, hgood₁, hsep₁, hc₂, h0₂, hgood₂, -, -⟩ :=
    eight_rect hκ8 hx h₁.path hg₁ hB₁ h₂.path hB₂ hF
  have hs₁ : IsStoppingTime 𝓖₁ fun ω => (eightS₁ x W₁ ζ₁ m ω : WithTop ℝ≥0) :=
    isStoppingTime_rect₁ (fun ω => (h₁.path ω).2.2.2.1) h₁.evol.2.1 (fun m => (hF.pp m).hull₁)
      (fun m => (goodSeq (-x) (![] : Fin 0 → ℝ) m).cap) m
  have hk : 0 < kh κ := by unfold kh; exact div_pos (by norm_num) (by linarith)
  set S₁ := eightS₁ x W₁ ζ₁ with hS₁def
  have hc₂t : ContinuousOn (Strip.extPath (W₂ · y₀)) (Icc 0 σ) := (hc₂ m y₀).mono (Icc_subset_Icc_right hσS)
  have hK₂ : fwdHull (frzPath W₂ (-x) σ y₀) σ ⊆ cofH₂ (-x) ![] m :=
    fwdHull_frzPath_subset (hc₂ m y₀) hσ.le hσS (hgood₂ m y₀).2
  have hlt : ∀ ω (s : ℝ≥0), s ≤ S₁ m ω → (s : ℝ≥0∞) < ζ₁ ω := fun ω s hs =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs) (hgood₁ m ω).1
  have hrec : ∀ x', IsSourceRecord (cofH₁ (-x) ![] m) (cofH₂ (-x) ![] m) (-x) (cofTm (-x) ![] m) (kh κ)
      (eightRR κ) (frzPath W₂ (-x) σ y₀) σ (eightRec κ (-x) W₁ VL₁ VR₁ W₂ S₁ m σ (x', y₀))
      (Strip.extPath (VL₁ 0 · x')) (Strip.extPath (VR₁ 0 · x')) (S₁ m x') := fun x' => by
    have hne' : ∀ s : ℝ≥0, 0 < s → s ≤ S₁ m x' → VL₁ 0 s x' ≠ W₁ s x' ∧ VR₁ 0 s x' ≠ W₁ s x' := fun s hs hsS =>
      hsep₁ x' s hs (hlt x' s hsS)
    exact isSourceRecord_eightRec (h₁.path x') rfl rfl (hgood₁ m x').1 (hgood₁ m x').2.1
      (fun s hs hsS => (hne' s hs hsS).1) (fun s hs hsS => (hne' s hs hsS).2) hc₂t (h0₂ y₀) hσ
      (hσS.trans (hgood₂ m y₀).1) (hgood₁ m x').2.2.1 (hF.pp m).sep_pos (hF.pp m).sep (hgood₁ m x').2.2.2 hK₂
  have hst := isColumnStoch_eightRec_of_reg (t₂ := σ) (y₀ := y₀) (W₂ := W₂) hk h₁ hB₁ hs₁
    (fun ω => (hgood₁ m ω).1) (fun ω s hs hsS => (hsep₁ ω s hs (hlt ω s hsS)).1)
    (fun ω s hs hsS => (hsep₁ ω s hs (hlt ω s hsS)).2)
    (fun ω s hsS => smallEight_sepP_of_good hx (h₁.path ω) (hg₁ ω) s (hlt ω s hsS))
  exact ⟨hF.pp m, isSourceColumn_of_stoch hrec hs₁ hst⟩

omit mY in
/-- The seeded measure of the column is the rectangle density at the height `σ`. -/
theorem seedMeasure_eightCol (κ x : ℝ) (P₁ : Measure X) (W₁ : ℝ≥0 → X → ℝ) (VL₁ : Fin 1 → ℝ≥0 → X → ℝ)
    (VR₁ : Fin 2 → ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞) (W₂ : ℝ≥0 → Y → ℝ) (m : ℕ) (σ : ℝ) (y₀ : Y) :
    seedMeasure P₁ (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ m σ y₀) (eightS₁ x W₁ ζ₁ m) =
      P₁.withDensity fun ω => ENNReal.ofReal (eightM κ x W₁ VL₁ VR₁ ζ₁ W₂ m (ω, y₀) (eightS₁ x W₁ ζ₁ m ω) σ) :=
  rfl

/-- **The per-sample frozen law of the small image curve** ((Eight), small-curve direction) at every protected frozen
time: under the rectangle density at height `σ ∈ (0, S₂ᵐ(y₀)]`, image data equal to the seeded capacity coordinates of
the column up to the cap satisfy `IsSeedSampleLaw`, with the residual as the noise. -/
theorem eight_isSeedSampleLaw {κ x : ℝ} (hκ8 : 8 ≤ κ) (hx : x < 0) {P₁ : Measure X} [IsProbabilityMeasure P₁]
    {𝓖₁ : Filtration ℝ≥0 mX} [𝓖₁.IsRightContinuous] {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
    {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ}
    {VL₂ : Fin 1 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}
    {P₂ : Measure Y} {𝓖₂ : Filtration ℝ≥0 mY}
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))
    (m : ℕ) (y₀ : Y) {σ : ℝ} (hσ : 0 < σ) (hσS : σ ≤ eightS₂ x W₂ ζ₂ m y₀)
    {W : ℝ≥0 → X → ℝ} {ζ : X → ℝ≥0∞} {VL : Fin 1 → ℝ≥0 → X → ℝ} {VR : Fin 2 → ℝ≥0 → X → ℝ}
    {N : ℝ≥0 → X → ℝ} {Scap : ℕ → X → ℝ≥0} {m' : ℕ}
    (hSm : ∀ ω, Scap m' ω = seedCapacityHorizon (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ m σ y₀) (eightS₁ x W₁ ζ₁ m) ω)
    (hW : ∀ ω t, t ≤ Scap m' ω →
      W t ω = seedCapacityDriver (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ m σ y₀) (eightS₁ x W₁ ζ₁ m) t ω)
    (hVL : ∀ ω i t, t ≤ Scap m' ω → VL i t ω =
      seedCapacityForce (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ m σ y₀) (eightS₁ x W₁ ζ₁ m) (eightChargeEquiv (.inl i)) t ω)
    (hVR : ∀ ω j t, t ≤ Scap m' ω → VR j t ω =
      seedCapacityForce (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ m σ y₀) (eightS₁ x W₁ ζ₁ m) (eightChargeEquiv (.inr j)) t ω)
    (hN : ∀ ω t, t ≤ Scap m' ω → N t ω = seedCapacityNoise (kh κ) (smallEightRhoL κ) (smallEightRhoR κ) (W · ω)
      (fun i t => VL i t ω) (fun j t => VR j t ω) t)
    (hζ : ∀ ω, (Scap m' ω : ℝ≥0∞) ≤ ζ ω)
    (Tk : ℕ → X → ℝ≥0) (hTk : ∀ k, IsStoppingTime 𝓖₁ fun ω => (Tk k ω : WithTop ℝ≥0))
    (hcap₁ : ∀ k ω, Tk k ω ≤ eightS₁ x W₁ ζ₁ m ω →
      (Scap k ω : ℝ) = (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ m σ y₀ ω).a (Tk k ω))
    (hcap₂ : ∀ k ω, eightS₁ x W₁ ζ₁ m ω ≤ Tk k ω → Scap m' ω ≤ Scap k ω) :
    IsSeedSampleLaw (P₁.withDensity fun ω =>
        ENNReal.ofReal (eightM κ x W₁ VL₁ VR₁ ζ₁ W₂ m (ω, y₀) (eightS₁ x W₁ ζ₁ m ω) σ))
      W ζ VL VR N Scap m' := by
  rw [← seedMeasure_eightCol]
  obtain ⟨hpp, hcol⟩ := eight_isSourceColumn hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m y₀ hσ hσS
  have hk : 0 < kh κ := by unfold kh; exact div_pos (by norm_num) (by linarith)
  obtain ⟨W₂', Vlo, Vhi, B, D, hrec, -⟩ := id hcol
  have hκd : ∀ ω, (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ m σ y₀ ω).κ = kh κ := fun ω =>
    congrArg SeedData.κ (hrec ω).source
  have hrd : ∀ ω, (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ m σ y₀ ω).r = eightRR κ := fun ω =>
    congrArg SeedData.r (hrec ω).source
  exact isSeedSampleLaw_of_seedColumn hpp hk hcol eightChargeEquiv
    (fun ω i => imageCharge_eight_left (by linarith) (hκd ω) (hrd ω) i)
    (fun ω j => imageCharge_eight_right (by linarith) (hκd ω) (hrd ω) j) hSm hW hVL hVR hN hζ Tk hTk hcap₁ hcap₂

end Column

end InteractingSLE.ZhanGT4.A1ELaw
