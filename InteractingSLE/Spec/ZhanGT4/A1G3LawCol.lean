/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3LawRect
import InteractingSLE.Spec.ZhanGT4.A1G3LawD10

/-!
# Zhan's A.1 under R83, (G3): the seeded (D10) on the G3 records

Packet PROVE-A1-G3LAW (R83). For regular G3 marginals in right-continuous filtrations with continuous Brownian paths
at every sample and a `GoodSmallG3` small curve at every sample (the patched marginals of A1-ASSEMBLE):

* **`g3_isSourceColumnG`**: at every frozen sample `y` and every frozen height `σ ∈ (0, S₂ᵐ(y)]`, the G3 records
  `x ↦ g3Rec κ (−y) … m σ (x, y)` form a mixed source column (`IsSourceColumnG`) of the cofinal protected pair `m`;
* **`g3ChargeEquiv`**, `imageCharge_g3Rec_*`: the enumeration of the image charges of the G3 records by the small
  image word (`smallG3RhoL`, `smallG3RhoR`): the left seed, the right seed, the ordinary mark, the other source;
* **`g3_seedCapacityBrownian`**: the seeded (D10) on G3's records — under the seeded measure of the column at height
  `σ`, the seeded image driver is a capacity Brownian motion of `seedFilt` with the small image word's charges.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3Law

open QuantumZipper (H fwdMap fwdHull)
open A2X A1Ref A1Canon A1Core A1Frozen A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin
  A1Asm A1Family Girsanov

/-! ### The charge enumeration of the small G3 image word -/

/-- **The image charges of the G3 records in the order of the small image word**: the left seed `y⁻` (mark `0`,
index `1`), then on the right the seed `y⁺` (mark `1`, index `2`), the ordinary mark `x` (mark `2`, index `3`) and the
other source (index `0`). -/
def g3ChargeEquiv : Fin 1 ⊕ Fin 3 ≃ Fin (3 + 1) where
  toFun := Sum.elim (fun _ => 1) ![2, 3, 0]
  invFun := ![Sum.inr 2, Sum.inl 0, Sum.inr 0, Sum.inr 1]
  left_inv := by
    intro i
    rcases i with i | i <;> fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem imageCharge_g3_left {κ : ℝ} (hκ : κ ≠ 0) {s : SeedData 3} (hsκ : s.κ = kh κ) (hsr : s.r = g3RR κ)
    (i : Fin 1) : s.imageCharge (g3ChargeEquiv (.inl i)) = smallG3RhoL κ i := by
  have hk : kh κ ≠ 0 := by unfold kh; exact div_ne_zero (by norm_num) hκ
  fin_cases i
  simp only [g3ChargeEquiv, Equiv.coe_fn_mk, Sum.elim_inl, SeedData.imageCharge, hsκ, hsr]
  show kh κ * g3RR κ 0 = smallG3RhoL κ 0
  simp only [g3RR, Matrix.cons_val_zero]
  field_simp

theorem imageCharge_g3_right {κ : ℝ} (hκ : κ ≠ 0) {s : SeedData 3} (hsκ : s.κ = kh κ) (hsr : s.r = g3RR κ)
    (j : Fin 3) : s.imageCharge (g3ChargeEquiv (.inr j)) = smallG3RhoR κ j := by
  have hk : kh κ ≠ 0 := by unfold kh; exact div_ne_zero (by norm_num) hκ
  fin_cases j
  · simp only [g3ChargeEquiv, Equiv.coe_fn_mk, Sum.elim_inr, SeedData.imageCharge, hsκ, hsr]
    show kh κ * g3RR κ 1 = smallG3RhoR κ 0
    simp only [g3RR, Matrix.cons_val_one, Matrix.cons_val_zero]
    field_simp
  · simp only [g3ChargeEquiv, Equiv.coe_fn_mk, Sum.elim_inr, SeedData.imageCharge, hsκ, hsr]
    show kh κ * g3RR κ 2 = smallG3RhoR κ 1
    simp only [g3RR, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    field_simp
  · simp only [g3ChargeEquiv, Equiv.coe_fn_mk, Sum.elim_inr, SeedData.imageCharge, hsκ]
    show -(kh κ / 2) = smallG3RhoR κ 2
    simp only [smallG3RhoR, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

/-! ### The source column at every frozen height and the seeded (D10) -/

section Column

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- **The G3 records at a frozen height form a mixed source column**: for regular G3 marginals with continuous
Brownian paths at every sample and a `GoodSmallG3` small curve at every sample, at every frozen sample `y₀` and every
height `σ ∈ (0, S₂ᵐ(y₀)]`, the records `x ↦ g3Rec κ (−y) … m σ (x, y₀)` of the cofinal protected pair `m` form an
`IsSourceColumnG` (with the records `IsSourceRecordG` at every sample), and the pair is protected
(`IsProtectedPairG`). -/
theorem g3_isSourceColumnG {κ x y : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) (hyx : y < x) (hx : x < 0) {P₁ : Measure X}
    {P₂ : Measure Y} {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY} [𝓖₁.IsRightContinuous]
    [𝓖₂.IsRightContinuous] {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 3 → ℝ≥0 → X → ℝ}
    {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ}
    {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallG3 (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))
    (m : ℕ) (y₀ : Y) {σ : ℝ} (hσ : 0 < σ) (hσS : σ ≤ g3S₂ x y W₂ ζ₂ m y₀) :
    IsProtectedPairG (cofGH₁ (-y) (x - y) ![x - y] m) (cofGH₂ (-y) (x - y) ![x - y] m)
        (cofGδ (-y) (x - y) ![x - y] m) (-y) (cofGq (-y) (x - y) ![x - y] m) (cofGd (-y) (x - y) ![x - y] m) ∧
      (∀ x', IsSourceRecordG (cofGH₁ (-y) (x - y) ![x - y] m) (cofGH₂ (-y) (x - y) ![x - y] m) (-y)
        (cofGq (-y) (x - y) ![x - y] m) (cofGTm (-y) (x - y) ![x - y] m) (kh κ) (g3RR κ) (frzPath W₂ (-y) σ y₀) σ
        (g3Rec κ (-y) W₁ VL₁ VR₁ W₂ (g3S₁ x y W₁ ζ₁) m σ (x', y₀)) (Strip.extPath (VL₁ 0 · x'))
        (Strip.extPath (VR₁ 0 · x')) (g3S₁ x y W₁ ζ₁ m x')) ∧
      IsSourceColumnG (cofGH₁ (-y) (x - y) ![x - y] m) (cofGH₂ (-y) (x - y) ![x - y] m) (-y)
        (cofGq (-y) (x - y) ![x - y] m) (cofGTm (-y) (x - y) ![x - y] m) (kh κ) (g3RR κ) 𝓖₁ P₁ σ
        (fun ω => g3Rec κ (-y) W₁ VL₁ VR₁ W₂ (g3S₁ x y W₁ ζ₁) m σ (ω, y₀)) (g3S₁ x y W₁ ζ₁ m) := by
  have hqlo : 0 < x - y := by linarith
  have hqlox : x - y < -y := by linarith
  have hne : (goodIdxG (-y) (x - y) ![x - y]).Nonempty :=
    goodIdxG_nonempty hqlo hqlox (fun m => by fin_cases m; simp; linarith) (fun m => by fin_cases m; simp; linarith)
  have hF := isEnclFamily_cofG hne
  obtain ⟨-, hgood₁, hsep₁, hsepO, hneP, hc₂, h0₂, hgood₂, -, -⟩ :=
    g3_rect hκ4 hκ8 hyx hx h₁.path hg₁ hB₁ h₂.path hB₂ hF
  have hs₁ : IsStoppingTime 𝓖₁ fun ω => (g3S₁ x y W₁ ζ₁ m ω : WithTop ℝ≥0) :=
    isStoppingTime_rect₁ (fun ω => (h₁.path ω).2.2.2.1) h₁.evol.2.1 (fun m => (hF.pp m).hull₁)
      (cofGN (-y) (x - y) ![x - y]) m
  have hk : 0 < kh κ := by unfold kh; exact div_pos (by norm_num) (by linarith)
  have hpp := isProtectedPairG_cofG hne
  set S₁ := g3S₁ x y W₁ ζ₁ with hS₁
  have hc₂t : ContinuousOn (Strip.extPath (W₂ · y₀)) (Icc 0 σ) := (hc₂ m y₀).mono (Icc_subset_Icc_right hσS)
  have hK₂ : fwdHull (frzPath W₂ (-y) σ y₀) σ ⊆ cofGH₂ (-y) (x - y) ![x - y] m :=
    fwdHull_frzPath_subset (hc₂ m y₀) hσ.le hσS (hgood₂ m y₀).2
  have hlt : ∀ ω (s : ℝ≥0), s ≤ S₁ m ω → (s : ℝ≥0∞) < ζ₁ ω := fun ω s hs =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs) (hgood₁ m ω).1
  have hrec : ∀ x', IsSourceRecordG (cofGH₁ (-y) (x - y) ![x - y] m) (cofGH₂ (-y) (x - y) ![x - y] m) (-y)
      (cofGq (-y) (x - y) ![x - y] m) (cofGTm (-y) (x - y) ![x - y] m) (kh κ) (g3RR κ) (frzPath W₂ (-y) σ y₀) σ
      (g3Rec κ (-y) W₁ VL₁ VR₁ W₂ S₁ m σ (x', y₀)) (Strip.extPath (VL₁ 0 · x')) (Strip.extPath (VR₁ 0 · x'))
      (S₁ m x') := fun x' => by
    have h2d : 0 < 2 * cofGd (-y) (x - y) ![x - y] m := by have := (hpp m).pair.rad_pos; positivity
    exact isSourceRecordG_g3Rec (h₁.path x') rfl rfl (by simp; linarith) (by simpa using qlo_le_cofGq hne m)
      (hgood₁ m x').1 (hgood₁ m x').2.1
      (fun s hs hsS => (hsep₁ x' s hs (hlt x' s hsS)).1) (fun s hs hsS => (hsep₁ x' s hs (hlt x' s hsS)).2)
      (fun s hsS => hsepO x' s (hlt x' s hsS)) h2d ((hpp m).pair.prot.mono_right subset_union_left)
      hc₂t (h0₂ y₀) hσ (hσS.trans (hgood₂ m y₀).1) (hgood₁ m x').2.2.1 (hpp m).pair.sep_pos
      (hpp m).pair.sep (hgood₁ m x').2.2.2 hK₂
  have hst := isColumnStoch_g3Rec_of_reg (t₂ := σ) (y₀ := y₀) (W₂ := W₂) hk h₁ hB₁ hs₁
    (fun ω => (hgood₁ m ω).1) (fun ω s hs hsS => (hsep₁ ω s hs (hlt ω s hsS)).1) (fun ω j s hs hsS => ?_)
    (fun ω s hsS => hneP ω s (hlt ω s hsS))
  · exact ⟨hpp m, hrec, isSourceColumnG_of_stoch hrec hs₁ hst⟩
  · fin_cases j
    · exact (hsep₁ ω s hs (hlt ω s hsS)).2
    · exact hsepO ω s (hlt ω s hsS)
    · exact hneP ω s (hlt ω s hsS)

/-- **The seeded (D10) on G3's records** (§A.1.3–A.1.4 for the small G3 curve): for regular G3 marginals with
continuous Brownian paths at every sample and a `GoodSmallG3` small curve at every sample, at every frozen sample `y₀`
and every height `σ ∈ (0, S₂ᵐ(y₀)]`, under the seeded measure of the column `x ↦ g3Rec κ (−y) … m σ (x, y₀)` (stopped
at the rectangle exit `S₁ᵐ`), the seeded image driver is a capacity Brownian motion of A1-FAMILY's `seedFilt` for the
small image word's charges `smallG3RhoL κ`, `smallG3RhoR κ` (enumerated by `g3ChargeEquiv`), with continuous paths. -/
theorem g3_seedCapacityBrownian {κ x y : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) (hyx : y < x) (hx : x < 0)
    {P₁ : Measure X} [IsProbabilityMeasure P₁] {P₂ : Measure Y} {𝓖₁ : Filtration ℝ≥0 mX}
    {𝓖₂ : Filtration ℝ≥0 mY} [𝓖₁.IsRightContinuous] [𝓖₂.IsRightContinuous] {W₁ : ℝ≥0 → X → ℝ}
    {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞}
    {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ}
    {ζ₂ : Y → ℝ≥0∞}
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallG3 (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))
    (m : ℕ) (y₀ : Y) {σ : ℝ} (hσ : 0 < σ) (hσS : σ ≤ g3S₂ x y W₂ ζ₂ m y₀) :
    let d : X → SeedData 3 := fun ω => g3Rec κ (-y) W₁ VL₁ VR₁ W₂ (g3S₁ x y W₁ ζ₁) m σ (ω, y₀)
    let T : X → ℝ≥0 := g3S₁ x y W₁ ζ₁ m
    ∃ B : ℝ≥0 → X → ℝ, ∃ (hCc : ∀ ω, Continuous (seedQuadClock (seedCapacityCoeff d T) ω))
      (hCm : ∀ ω, Monotone (seedQuadClock (seedCapacityCoeff d T) ω))
      (hcm : ∀ u : ℝ≥0, Measurable[𝓖₁ u] fun ω => seedQuadClock (seedCapacityCoeff d T) ω u),
      SeedCapacityBrownian (kh κ) (smallG3RhoL κ) (smallG3RhoR κ) (seedMeasure P₁ d T)
        (A1Family.seedFilt 𝓖₁ d T hCc hCm hcm) (seedCapacityDriver d T)
        (fun i => seedCapacityForce d T (g3ChargeEquiv (.inl i)))
        (fun j => seedCapacityForce d T (g3ChargeEquiv (.inr j))) (seedCapacityHorizon d T)
        (A1Family.seedBh (kh κ) d T (girsanovProcess B (seedNoise (kh κ) d T))) ∧
      ∀ ω, Continuous (A1Family.seedBh (kh κ) d T (girsanovProcess B (seedNoise (kh κ) d T)) · ω) := by
  intro d T
  have hqlo : 0 < x - y := by linarith
  have hqlox : x - y < -y := by linarith
  have hne : (goodIdxG (-y) (x - y) ![x - y]).Nonempty :=
    goodIdxG_nonempty hqlo hqlox (fun m => by fin_cases m; simp; linarith) (fun m => by fin_cases m; simp; linarith)
  have hF := isEnclFamily_cofG hne
  obtain ⟨-, hgood₁, -, hsepO, -, -, -, -, -, -⟩ :=
    g3_rect hκ4 hκ8 hyx hx h₁.path hg₁ hB₁ h₂.path hB₂ hF
  have hk : 0 < kh κ := by unfold kh; exact div_pos (by norm_num) (by linarith)
  obtain ⟨hpp, hrec, hcol⟩ := g3_isSourceColumnG hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ m y₀ hσ hσS
  have hrate : ∀ ω m', ∀ t ∈ Icc (0 : ℝ) (T ω),
      IntervalIntegrable (fun u => 2 / ((d ω).V m' u - (d ω).W u)) volume 0 t := by
    intro ω m' t ht
    fin_cases m'
    · exact (hrec ω).lo.integrable t ht
    · exact (hrec ω).hi.integrable t ht
    · refine intervalIntegrable_rate_of_ne (hrec ω).own.cont.continuousOn ((hrec ω).mark 2).cont
        (fun u hu => ?_) t ht
      have hu0 : (0 : ℝ) ≤ u := hu.1
      have huS : u.toNNReal ≤ g3S₁ x y W₁ ζ₁ m ω := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hu0]; exact hu.2
      have hW : (d ω).W u = W₁ u.toNNReal ω := eightDrv_eqOn W₁ (g3S₁ x y W₁ ζ₁) m ω hu
      have hV : (d ω).V 2 u = VR₁ 1 u.toNNReal ω := rfl
      rw [hV, hW]
      exact hsepO ω _ (lt_of_le_of_lt (ENNReal.coe_le_coe.2 huS) (hgood₁ m ω).1)
  have hκd : ∀ ω, (d ω).κ = kh κ := fun ω => congrArg SeedData.κ (hrec ω).source
  have hrd : ∀ ω, (d ω).r = g3RR κ := fun ω => congrArg SeedData.r (hrec ω).source
  exact exists_seedCapacityBrownian_of_column hpp hk hcol hrate g3ChargeEquiv
    (fun ω i => imageCharge_g3_left (by linarith) (hκd ω) (hrd ω) i)
    (fun ω j => imageCharge_g3_right (by linarith) (hκd ω) (hrd ω) j)

end Column

end InteractingSLE.ZhanGT4.A1G3Law
