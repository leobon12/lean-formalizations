/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1ESndFam
import InteractingSLE.Spec.ZhanGT4.A1G3L2SndId
import InteractingSLE.Spec.ZhanGT4.A1GoodRepl

/-!
# Zhan's A.1 under R83, (Eight), small-curve direction: the canonical data are the seeded capacity coordinates

Packet PROVE-A1-EIGHTSND (mirror of PROVE-A1-G3LAW2's `A1G3L2SndId`/`A1G3L2Clock`). For the patched Eight marginals,
at a frozen sample `y₀`, a protected frozen time `σ ∈ (0, S₂ᵏ(y₀)]` and every small sample `x₀`:

* **`clock_facts_of_seedColumn`**: the capacity clock of a seed source column (`IsSourceColumn`) is continuous, strictly
  increasing and bounded below linearly (A1-EIGHTLAW's seed-column (D10) derivation, exposed);
* **`eight_isSourceRecord`**: the Eight records at a frozen height are source records against the frozen path
  `frzPath W₂ (−x) σ y₀` (the record half of A1-EIGHTLAW's `eight_isSourceColumn`, with the frozen path named);
* **`eightCol_facts`**: `OwnData` of the record in the physical frame (`physHull (0 − x) …`), agreement of its driver
  with the small driver on `[0, S₁ᵏ]`, the good horizon `S₁ᵏ(x₀)` (PROVE-A1-GOODTIME's `eightSnd_isGoodTime`);
* **`eightSnd_rDrv_eq`**, **`eightSnd_cap_eq`**, `eightSnd_cap_eq_clk`, **`eightSnd_cap_le_cap`**: the masked
  canonical image driver is the seeded capacity driver, the raw caps are the capacity horizon, the clock of the record
  at the own times of the other rectangles, and are monotone in those own times.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1ESnd

open QuantumZipper (H fwdHull fwdMap IsForwardSol)
open A2X A1Ref A1Canon A1Core A1Frozen A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin
  A1Asm A1Family A1Forces A1RLaw A1LargeDens A1ELaw A1G3L2 Girsanov A1MultiMark

/-! ### The clock facts of a seed source column -/

section Clock

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The clock facts of a seed source column**: the capacity clock is continuous and strictly increasing at every
sample and bounded below by `c · r` for some `c > 0`. -/
theorem clock_facts_of_seedColumn {n : ℕ} {H₁ H₂ : Set ℂ} {δ p q dd Tm κ : ℝ} {rr : Fin n → ℝ}
    {𝓕 : Filtration ℝ≥0 mΩ} {P : Measure Ω} [IsProbabilityMeasure P] {t₂ : ℝ} {sdata : Ω → SeedData n}
    {T : Ω → ℝ≥0} (hpp : IsProtectedPair H₁ H₂ δ p q dd)
    (hcol : IsSourceColumn H₁ H₂ p Tm κ rr 𝓕 P t₂ sdata T) :
    (∀ ω, Continuous (seedQuadClock (seedCapacityCoeff sdata T) ω)) ∧
      (∀ ω, StrictMono (seedQuadClock (seedCapacityCoeff sdata T) ω)) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ ω r, c * r ≤ seedQuadClock (seedCapacityCoeff sdata T) ω r := by
  obtain ⟨W₂, Vlo, Vhi, B, D, hrec, hT, hB, hBc, hDm, hDc, hdW, -, hVm, -, -⟩ := hcol
  obtain ⟨x₀⟩ : Nonempty Ω := by
    by_contra hX
    have hE : IsEmpty Ω := not_nonempty_iff.1 hX
    have h1 := measure_univ (μ := P)
    rw [Set.univ_eq_empty_iff.2 hE, measure_empty] at h1
    exact zero_ne_one h1
  have r₀ := hrec x₀
  have hH₁ := hpp.hull₁
  have hH₂ := hpp.hull₂
  have hδ := hpp.sep_pos
  have hsep := hpp.sep
  have hq := hpp.prot_pos
  have hqp := hpp.prot_lt
  have hd := hpp.rad_pos
  have hqH := hpp.prot
  have hW₂ := r₀.contW₂
  have hW₂0 := r₀.zeroW₂
  have ht₂ := r₀.pos₂
  have ht₂m := r₀.le₂
  have hK₂ := r₀.sub₂
  have hTm : ∀ ω, (T ω : ℝ) ≤ Tm := fun ω => (hrec ω).le₁
  have hdsource := fun ω => (hrec ω).source
  have hK₁ := fun ω => (hrec ω).sub₁
  have hVI := fun ω => (hrec ω).marks
  have hdκ : ∀ ω, (sdata ω).κ = κ := fun ω => congrArg SeedData.κ (hdsource ω)
  have hdr : ∀ ω, (sdata ω).r = rr := fun ω => congrArg SeedData.r (hdsource ω)
  have hdφ : ∀ ω, (sdata ω).φ = (fun z => fwdMap W₂ t₂ z + W₂ t₂) :=
    fun ω => congrArg SeedData.φ (hdsource ω)
  have hdζ : ∀ ω, (sdata ω).ζ₀ = W₂ t₂ := fun ω => congrArg SeedData.ζ₀ (hdsource ω)
  have h : ∀ ω, OwnData (sdata ω).W (fwdHull W₂ t₂) (sdata ω).φ (T ω) (sdata ω).a (sdata ω).W' :=
    fun ω => (hrec ω).own
  have hown : ∀ ω, OwnData (sdata ω).W (fwdHull W₂ t₂)
      (fun z => fwdMap W₂ t₂ z + W₂ t₂) (T ω) (sdata ω).a (sdata ω).W' := by
    intro ω
    rw [← hdφ ω]
    exact h ω
  have hW0H : ∀ ω, ((sdata ω).W 0 : ℂ) ∈ closure H₁ := fun ω =>
    closure_mono (hK₁ ω) (start_mem_closure_fwdHull (h ω).cont (h ω).pos)
  have hW₂H : (W₂ 0 : ℂ) ∈ closure H₂ := by rw [hW₂0]; exact hpp.src
  have hWq : ∀ ω, (sdata ω).W 0 < q := fun ω => by rw [(h ω).zero]; exact hq
  obtain ⟨r, L₀, hr, -, hinterval⟩ := exists_seed_interval_own_bounds_right hH₁ hH₂ hδ hsep hd hqH Tm
  have hint : ∀ ω u, u ∈ Icc (0 : ℝ) (T ω) → ∀ x ∈ uIcc (Vlo ω u) (Vhi ω u),
      Disjoint (ball (x : ℂ) r)
        ((fun z => fwdMap (sdata ω).W u z + (sdata ω).W u) '' fwdHull W₂ t₂) := by
    intro ω u hu x hx
    exact (hinterval (sdata ω).W W₂ (Vlo ω) (Vhi ω) (T ω) t₂
      (sdata ω).a (sdata ω).W' (hown ω) hW₂ ht₂ (hW0H ω) hW₂H (hWq ω)
      (by rw [hW₂0]; exact hqp) ht₂m (hK₁ ω) hK₂ ((hrec ω).lo) ((hrec ω).hi) u hu x hx).1
  obtain ⟨r₀', a₀, γ, Γ, lam, hr₀, ha₀, -, hd9⟩ :=
    exists_twoCurveD9 hH₁ hH₂ hδ hsep hd hq hqH
      (p := (Fin.elim0 : Fin 0 → ℝ)) (fun m => Fin.elim0 m) (fun m => Fin.elim0 m) Tm
  have hd9ω := fun ω => hd9 (sdata ω).W W₂ t₂ (T ω) (sdata ω).a (sdata ω).W'
    0 Fin.elim0 (hown ω) hW₂ hW₂H (by rwa [hW₂0]) ht₂ ht₂m (hTm ω) (hK₁ ω) hK₂
  have hv₀ : ∀ ω, ∃ v, IsForwardSol (sdata ω).W' (sdata ω).ζ₀ ((sdata ω).a (T ω)) v := by
    intro ω
    rw [hdζ ω]
    exact (hd9ω ω).alive₀
  let X : ℝ≥0 → Ω → ℝ := fun u ω => Real.sqrt κ * B u ω + D u ω
  have hXm : ∀ u, Measurable[𝓕 u] (X u) := fun u => ((hB.2.1 u).const_mul _).add (hDm u)
  have hXc : ∀ ω, Continuous (X · ω) := fun ω => ((hBc ω).const_mul _).add (hDc ω)
  have hdX : ∀ ω, (sdata ω).W = Ito.rpath (X · ω) := by
    intro ω
    rw [hdW ω, driftDriver_eq_rpath]
  have hmclr : ∀ ω m, ∀ t ∈ Icc (0 : ℝ) (T ω),
      Disjoint (ball ((sdata ω).V m t : ℂ) r) ((fun z => fwdMap (sdata ω).W t z + (sdata ω).W t) '' fwdHull W₂ t₂) :=
    fun ω m u hu => hint ω u hu _ (hVI ω u hu m)
  obtain ⟨hmA, hcA, hbA⟩ := seedMap_alive_derivative_facts hXm hXc hdX hdφ hdζ hdκ hdr hT hr₀ hr h hv₀
    (fun ω t ht => (hd9ω ω).d9.clr t ht) (fun ω m t ht => hmclr ω m t ht) hVm
  have hm : ∀ u, Measurable[𝓕 u] ({ω | u ≤ T ω}.indicator fun ω => (sdata ω).A 1 u - 1) := fun u => by
    have hg : MeasurableSet[𝓕 u] {ω | u ≤ T ω} := measurableSet_ge_of_isStoppingTime hT u
    have e' : ({ω | u ≤ T ω}.indicator fun ω => (sdata ω).A 1 u - 1) =
        ({ω | u ≤ T ω}.indicator fun ω => (sdata ω).A 1 u) - {ω | u ≤ T ω}.indicator fun _ => (1 : ℝ) := by
      funext ω
      by_cases hω : ω ∈ {ω | u ≤ T ω}
      · simp only [indicator_of_mem hω, Pi.sub_apply]
      · simp only [indicator_of_notMem hω, Pi.sub_apply, sub_zero]
    rw [e']
    exact (hmA u).sub (measurable_const.indicator hg)
  have hA1 : ∀ ω u, 0 < u → u ≤ T ω → a₀ ≤ (sdata ω).A 1 u := fun ω u hu huT => by
    change a₀ ≤ frzA (sdata ω).W (sdata ω).W' (sdata ω).a (sdata ω).φ 1 u
    rw [hdφ ω]
    exact (hd9ω ω).d9.A1 u ⟨u.coe_nonneg, NNReal.coe_le_coe.2 huT⟩
  obtain ⟨hCc, hCs, -, c, hc, hClb⟩ := clock_props hm hcA ha₀ (C := 1) (fun ω u hu huT => hbA u ω hu huT) hA1
  exact ⟨hCc, hCs, c, hc, hClb⟩

end Clock

/-! ### The Eight records against the named frozen path -/

section Rec

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
  {κ x : ℝ} {P₁ : Measure X} {P₂ : Measure Y} {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY}
  {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ}
  {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ}
  {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}

/-- The rectangle facts of the Eight assembly (`eight_rect` on the cofinal family). -/
theorem eight_rect_facts (hκ8 : 8 ≤ κ) (hx : x < 0)
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω)) :
    (∀ m ω, (eightS₁ x W₁ ζ₁ m ω : ℝ≥0∞) < ζ₁ ω ∧ 0 < (eightS₁ x W₁ ζ₁ m ω : ℝ)) ∧
    (∀ ω (s : ℝ≥0), 0 < s → (s : ℝ≥0∞) < ζ₁ ω → VL₁ 0 s ω ≠ W₁ s ω ∧ VR₁ 0 s ω ≠ W₁ s ω) ∧
    (∀ m ω, (eightS₂ x W₂ ζ₂ m ω : ℝ≥0∞) < ζ₂ ω) ∧ (∀ m ω, 0 < (eightS₂ x W₂ ζ₂ m ω : ℝ)) := by
  have hx₂ : 0 < -x := by linarith
  have hne : (goodIdx (-x) (![] : Fin 0 → ℝ)).Nonempty :=
    goodIdx_nonempty hx₂ (fun m => m.elim0) (fun m => m.elim0)
  obtain ⟨-, hgood₁, hsep₁, -, -, -, hS₂pos, hS₂ζ⟩ :=
    eight_rect hκ8 hx h₁.path hg₁ hB₁ h₂.path hB₂ (isEnclFamily_cof hne)
  exact ⟨fun m ω => ⟨(hgood₁ m ω).1, (hgood₁ m ω).2.1⟩, hsep₁, hS₂ζ, hS₂pos⟩

/-- **The Eight records at a frozen height are source records against the frozen path** `frzPath W₂ (−x) σ y₀`
(the record half of A1-EIGHTLAW's `eight_isSourceColumn`). -/
theorem eight_isSourceRecord (hκ8 : 8 ≤ κ) (hx : x < 0)
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))
    (m : ℕ) (y₀ : Y) {σ : ℝ} (hσ : 0 < σ) (hσS : σ ≤ eightS₂ x W₂ ζ₂ m y₀) (x' : X) :
    IsSourceRecord (cofH₁ (-x) ![] m) (cofH₂ (-x) ![] m) (-x) (cofTm (-x) ![] m) (kh κ) (eightRR κ)
      (frzPath W₂ (-x) σ y₀) σ (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ m σ y₀ x') (Strip.extPath (VL₁ 0 · x'))
      (Strip.extPath (VR₁ 0 · x')) (eightS₁ x W₁ ζ₁ m x') := by
  have hx₂ : 0 < -x := by linarith
  have hne : (goodIdx (-x) (![] : Fin 0 → ℝ)).Nonempty :=
    goodIdx_nonempty hx₂ (fun m => m.elim0) (fun m => m.elim0)
  have hF := isEnclFamily_cof hne
  obtain ⟨-, hgood₁, hsep₁, hc₂, h0₂, hgood₂, -, -⟩ :=
    eight_rect hκ8 hx h₁.path hg₁ hB₁ h₂.path hB₂ hF
  have hc₂t : ContinuousOn (Strip.extPath (W₂ · y₀)) (Icc 0 σ) := (hc₂ m y₀).mono (Icc_subset_Icc_right hσS)
  have hK₂ : fwdHull (frzPath W₂ (-x) σ y₀) σ ⊆ cofH₂ (-x) ![] m :=
    fwdHull_frzPath_subset (hc₂ m y₀) hσ.le hσS (hgood₂ m y₀).2
  have hlt : ∀ (s : ℝ≥0), s ≤ eightS₁ x W₁ ζ₁ m x' → (s : ℝ≥0∞) < ζ₁ x' := fun s hs =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs) (hgood₁ m x').1
  have hne' : ∀ s : ℝ≥0, 0 < s → s ≤ eightS₁ x W₁ ζ₁ m x' → VL₁ 0 s x' ≠ W₁ s x' ∧ VR₁ 0 s x' ≠ W₁ s x' :=
    fun s hs hsS => hsep₁ x' s hs (hlt s hsS)
  exact isSourceRecord_eightRec (h₁.path x') rfl rfl (hgood₁ m x').1 (hgood₁ m x').2.1
    (fun s hs hsS => (hne' s hs hsS).1) (fun s hs hsS => (hne' s hs hsS).2) hc₂t (h0₂ y₀) hσ
    (hσS.trans (hgood₂ m y₀).1) (hgood₁ m x').2.2.1 (hF.pp m).sep_pos (hF.pp m).sep (hgood₁ m x').2.2.2 hK₂

end Rec

/-! ### The per-sample facts of the column -/

section Col

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
  {κ x : ℝ} {P₁ : Measure X} {P₂ : Measure Y} {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY}
  [𝓖₁.IsRightContinuous] {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ}
  {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Y → ℝ}
  {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}

variable (hκ8 : 8 ≤ κ) (hx : x < 0)
  (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
  (hB₁ : ∀ ω, Continuous (B₁ · ω))
  (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
  (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))

include hκ8 hx h₁ hB₁ hg₁ h₂ hB₂

omit [𝓖₁.IsRightContinuous] in
/-- **The per-sample facts of the column** at a protected frozen time `σ ∈ (0, S₂ᵏ(y₀)]`: the record is an image chain
of the small curve in the physical frame (`OwnData` against `physHull (0 − x) …`, `physMap (0 − x) …`), its driver is
the small driver on `[0, S₁ᵏ]`, `S₁ᵏ(x₀)` is a good horizon, and the large driver is continuous a little beyond `σ`. -/
theorem eightCol_facts (k : ℕ) (y₀ : Y) {σ : ℝ≥0} (hσ : 0 < σ) (hσS : σ ≤ eightS₂ x W₂ ζ₂ k y₀) (x₀ : X) :
    OwnData (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀ x₀).W (physHull (0 - x) (Strip.extPath (W₂ · y₀)) σ)
        (physMap (0 - x) (Strip.extPath (W₂ · y₀)) σ) (eightS₁ x W₁ ζ₁ k x₀)
        (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀ x₀).a (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀ x₀).W' ∧
      EqOn (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀ x₀).W (Strip.extPath (W₁ · x₀)) (Icc 0 (eightS₁ x W₁ ζ₁ k x₀)) ∧
      A1Ref.IsGoodTime x (Strip.extPath (W₁ · x₀)) (ζ₁ x₀) 0 (Strip.extPath (W₂ · y₀)) σ (eightS₁ x W₁ ζ₁ k x₀) ∧
      ∃ τ', (σ : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (W₂ · y₀)) (Icc 0 τ') := by
  obtain ⟨-, -, hS₂ζ, -⟩ := eight_rect_facts hκ8 hx h₁ hB₁ hg₁ h₂ hB₂
  have r := eight_isSourceRecord hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ (σ := (σ : ℝ)) (by exact_mod_cast hσ)
    (by exact_mod_cast hσS) x₀
  have hσζ : (σ : ℝ≥0∞) < ζ₂ y₀ := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hσS) (hS₂ζ k y₀)
  have hk := A1Ref.exists_continuousOn_extPath_beyond (h₂.path y₀).2.2.2.1 hσζ
  have hown0 := r.own
  have hφ : (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀ x₀).φ = frzChart (frzPath W₂ (-x) σ y₀) σ :=
    congrArg SeedData.φ r.source
  rw [hφ, fwdHull_frzPath_eq W₂ (-x) σ.coe_nonneg y₀ hk, frzChart_frzPath_eq W₂ (-x) σ.coe_nonneg y₀] at hown0
  have hown : OwnData (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀ x₀).W (physHull (0 - x) (Strip.extPath (W₂ · y₀)) σ)
      (physMap (0 - x) (Strip.extPath (W₂ · y₀)) σ) (eightS₁ x W₁ ζ₁ k x₀)
      (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀ x₀).a (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀ x₀).W' := by
    rw [zero_sub]
    exact hown0
  exact ⟨hown, eightDrv_eqOn W₁ (eightS₁ x W₁ ζ₁) k x₀,
    (A1Good.eightSnd_isGoodTime hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k x₀ y₀ hσS).1, hk⟩

/-- **The clock facts of the column** at a protected frozen time. -/
theorem eightCol_clock [IsProbabilityMeasure P₁] (k : ℕ) (y₀ : Y) {σ : ℝ≥0} (hσ : 0 < σ)
    (hσS : σ ≤ eightS₂ x W₂ ζ₂ k y₀) :
    (∀ ω, Continuous (seedQuadClock (seedCapacityCoeff (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀)
      (eightS₁ x W₁ ζ₁ k)) ω)) ∧
    (∀ ω, StrictMono (seedQuadClock (seedCapacityCoeff (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀)
      (eightS₁ x W₁ ζ₁ k)) ω)) ∧
    ∃ c : ℝ, 0 < c ∧ ∀ ω r, c * r ≤ seedQuadClock (seedCapacityCoeff (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀)
      (eightS₁ x W₁ ζ₁ k)) ω r := by
  obtain ⟨hpp, hcol⟩ := eight_isSourceColumn hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ (σ := (σ : ℝ)) (by exact_mod_cast hσ)
    (by exact_mod_cast hσS)
  exact clock_facts_of_seedColumn hpp hcol

/-- The own time of the raw cap `k'` as a function of the small sample (`eightSndOwn` at the frozen sample `y₀`). -/
def eightSndTk (x : ℝ) (W₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞) (W₂ : ℝ≥0 → Y → ℝ) (ζ₂ : Y → ℝ≥0∞) (σ : ℝ≥0)
    (y₀ : Y) (k' : ℕ) (x₀ : X) : ℝ≥0 :=
  if σ ≤ eightS₂ x W₂ ζ₂ k' y₀ then eightS₁ x W₁ ζ₁ k' x₀ else 0

/-- **The masked canonical image driver is the seeded capacity driver** up to the capacity horizon (live frozen
sample, protected frozen time). -/
theorem eightSnd_rDrv_eq [IsProbabilityMeasure P₁] (k : ℕ) (y₀ : Y) {σ : ℝ≥0} (hσ : 0 < σ)
    (hσS : σ ≤ eightS₂ x W₂ ζ₂ k y₀) (hlive : eightSndLive W₂ VL₂ ζ₂ σ y₀) (x₀ : X) {t : ℝ≥0}
    (ht : t ≤ seedCapacityHorizon (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀) (eightS₁ x W₁ ζ₁ k) x₀) :
    rDrv (eightSndLive W₂ VL₂ ζ₂) x W₁ ζ₁ 0 W₂ (fun _ => σ) t (x₀, y₀) =
      seedCapacityDriver (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀) (eightS₁ x W₁ ζ₁ k) t x₀ := by
  obtain ⟨hown, hWj, hgood, hk⟩ := eightCol_facts hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS x₀
  have hrec := fun ω => eight_isSourceRecord hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ (σ := (σ : ℝ)) (by exact_mod_cast hσ)
    (by exact_mod_cast hσS) ω
  obtain ⟨hCc, hCs, c, hc, hClb⟩ := eightCol_clock hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS
  have hj : ∀ T : ℝ, ENNReal.ofReal T < ζ₁ x₀ → ContinuousOn (Strip.extPath (W₁ · x₀)) (Icc 0 T) :=
    fun T hT => A1Ref.continuousOn_extPath_Icc (h₁.path x₀).2.2.2.1 hT
  have ht' : (t : ℝ) ≤ (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀ x₀).a (eightS₁ x W₁ ζ₁ k x₀) := by
    rw [← coe_seedCapacityHorizon (fun ω => (hrec ω).own) x₀]
    exact_mod_cast ht
  rw [seedCapacityDriver_eq_sub (fun ω => (hrec ω).own) hCc hCs hc hClb x₀ ht,
    ← imgDrv_sub_eq_of_ownData hown hWj hj (A1Ref.extPath_zero_of (h₁.path x₀).1) hk
      (A1Ref.extPath_zero_of (h₂.path y₀).1) σ.coe_nonneg hgood t.coe_nonneg ht']
  simp only [rDrv, cImgDrvM, cImgDrv, cImgSrc, ite_eq_left hlive]

omit [𝓖₁.IsRightContinuous] in
/-- **The raw cap `k'` at a good own time is the clock there** (any rectangle `k'` with an open gate). -/
theorem eightSnd_cap_eq_imgClk (k' : ℕ) (y₀ : Y) {σ : ℝ≥0} (hσ : 0 < σ) (hσS : σ ≤ eightS₂ x W₂ ζ₂ k' y₀)
    (hlive : eightSndLive W₂ VL₂ ζ₂ σ y₀) (x₀ : X) :
    eightSndCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ σ k' (x₀, y₀) =
      (A1Ref.imgClk x (Strip.extPath (W₁ · x₀)) 0 (Strip.extPath (W₂ · y₀)) σ
        (eightS₁ x W₁ ζ₁ k' x₀)).toNNReal := by
  obtain ⟨-, -, hgood, hk⟩ := eightCol_facts hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k' y₀ hσ hσS x₀
  have hT : eightSndOwn x W₁ ζ₁ W₂ ζ₂ σ k' (x₀, y₀) = (eightS₁ x W₁ ζ₁ k' x₀ : ℝ) := by
    simp only [eightSndOwn, hσS, ↓reduceIte]
  unfold eightSndCap
  rw [capSnd_congr_pt (T' := fun _ => (eightS₁ x W₁ ζ₁ k' x₀ : ℝ)) hT]
  exact capSnd_eq_of_isGoodTime (T := fun _ => (eightS₁ x W₁ ζ₁ k' x₀ : ℝ)) hlive
    (fun T hT => A1Ref.continuousOn_extPath_Icc (h₁.path x₀).2.2.2.1 hT) (h₁.path x₀).1 hk (h₂.path y₀).1 hgood

omit [𝓖₁.IsRightContinuous] in
/-- **The raw cap `k` is the capacity horizon of the column** (live frozen sample, protected frozen time). -/
theorem eightSnd_cap_eq (k : ℕ) (y₀ : Y) {σ : ℝ≥0} (hσ : 0 < σ) (hσS : σ ≤ eightS₂ x W₂ ζ₂ k y₀)
    (hlive : eightSndLive W₂ VL₂ ζ₂ σ y₀) (x₀ : X) :
    eightSndCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ σ k (x₀, y₀) =
      seedCapacityHorizon (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀) (eightS₁ x W₁ ζ₁ k) x₀ := by
  obtain ⟨hown, hWj, hgood, hk⟩ := eightCol_facts hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS x₀
  rw [eightSnd_cap_eq_imgClk hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS hlive x₀,
    (imgClk_imgDrv_eqOn_of_ownData hown hWj (fun T hT => A1Ref.continuousOn_extPath_Icc (h₁.path x₀).2.2.2.1 hT)
      (A1Ref.extPath_zero_of (h₁.path x₀).1) hk (A1Ref.extPath_zero_of (h₂.path y₀).1) σ.coe_nonneg hgood).1
      ⟨NNReal.coe_nonneg _, le_rfl⟩]
  rfl

omit [𝓖₁.IsRightContinuous] in
/-- **The other raw caps below the horizon are the clock of the column** (A1-FAMILY's `hcap₁`). -/
theorem eightSnd_cap_eq_clk (k : ℕ) (y₀ : Y) {σ : ℝ≥0} (hσ : 0 < σ) (hσS : σ ≤ eightS₂ x W₂ ζ₂ k y₀)
    (hlive : eightSndLive W₂ VL₂ ζ₂ σ y₀) (k' : ℕ) (x₀ : X)
    (hle : eightSndTk x W₁ ζ₁ W₂ ζ₂ σ y₀ k' x₀ ≤ eightS₁ x W₁ ζ₁ k x₀) :
    (eightSndCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ σ k' (x₀, y₀) : ℝ) =
      (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀ x₀).a (eightSndTk x W₁ ζ₁ W₂ ζ₂ σ y₀ k' x₀) := by
  obtain ⟨hown, hWj, hgood, hk⟩ := eightCol_facts hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS x₀
  have hclk := (imgClk_imgDrv_eqOn_of_ownData hown hWj
    (fun T hT => A1Ref.continuousOn_extPath_Icc (h₁.path x₀).2.2.2.1 hT) (A1Ref.extPath_zero_of (h₁.path x₀).1) hk
    (A1Ref.extPath_zero_of (h₂.path y₀).1) σ.coe_nonneg hgood).1
  by_cases hg : σ ≤ eightS₂ x W₂ ζ₂ k' y₀
  · have hTk : eightSndTk x W₁ ζ₁ W₂ ζ₂ σ y₀ k' x₀ = eightS₁ x W₁ ζ₁ k' x₀ := by
      simp only [eightSndTk, hg, ↓reduceIte]
    rw [hTk] at hle ⊢
    have hmem : ((eightS₁ x W₁ ζ₁ k' x₀ : ℝ≥0) : ℝ) ∈ Icc (0 : ℝ) (eightS₁ x W₁ ζ₁ k x₀) :=
      ⟨NNReal.coe_nonneg _, by exact_mod_cast hle⟩
    rw [eightSnd_cap_eq_imgClk hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k' y₀ hσ hg hlive x₀, hclk hmem]
    have h0 : 0 ≤ (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀ x₀).a (eightS₁ x W₁ ζ₁ k' x₀) := by
      rw [← hown.a0]
      exact hown.mono.monotoneOn ⟨le_rfl, hown.pos.le⟩ hmem hmem.1
    exact Real.coe_toNNReal _ h0
  · have hTk : eightSndTk x W₁ ζ₁ W₂ ζ₂ σ y₀ k' x₀ = 0 := by simp only [eightSndTk, hg, ↓reduceIte]
    rw [hTk, NNReal.coe_zero, hown.a0]
    unfold eightSndCap
    rw [capSnd_of_nonpos]
    · rfl
    · simp only [eightSndOwn, hg, ↓reduceIte, le_refl]

omit [𝓖₁.IsRightContinuous] in
/-- **The raw caps are monotone in the own times** (A1-FAMILY's `hcap₂`). -/
theorem eightSnd_cap_le_cap (k : ℕ) (y₀ : Y) {σ : ℝ≥0} (hσ : 0 < σ) (hσS : σ ≤ eightS₂ x W₂ ζ₂ k y₀)
    (hlive : eightSndLive W₂ VL₂ ζ₂ σ y₀) (k' : ℕ) (x₀ : X)
    (hle : eightS₁ x W₁ ζ₁ k x₀ ≤ eightSndTk x W₁ ζ₁ W₂ ζ₂ σ y₀ k' x₀) :
    eightSndCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ σ k (x₀, y₀) ≤
      eightSndCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ σ k' (x₀, y₀) := by
  obtain ⟨hR1, -, -, -⟩ := eight_rect_facts hκ8 hx h₁ hB₁ hg₁ h₂ hB₂
  by_cases hg : σ ≤ eightS₂ x W₂ ζ₂ k' y₀
  · have hTk : eightSndTk x W₁ ζ₁ W₂ ζ₂ σ y₀ k' x₀ = eightS₁ x W₁ ζ₁ k' x₀ := by
      simp only [eightSndTk, hg, ↓reduceIte]
    rw [hTk] at hle
    obtain ⟨-, -, hgood', hk⟩ := eightCol_facts hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k' y₀ hσ hg x₀
    rw [eightSnd_cap_eq_imgClk hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS hlive x₀,
      eightSnd_cap_eq_imgClk hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k' y₀ hσ hg hlive x₀]
    obtain ⟨-, hmono, -⟩ := exists_isImgDrvOn (fun T hT => A1Ref.continuousOn_extPath_Icc (h₁.path x₀).2.2.2.1 hT)
      (A1Ref.extPath_zero_of (h₁.path x₀).1) hk (A1Ref.extPath_zero_of (h₂.path y₀).1) σ.coe_nonneg hgood'
    exact Real.toNNReal_le_toNNReal (hmono.monotoneOn ⟨NNReal.coe_nonneg _, by exact_mod_cast hle⟩
      ⟨NNReal.coe_nonneg _, le_rfl⟩ (by exact_mod_cast hle))
  · have hTk : eightSndTk x W₁ ζ₁ W₂ ζ₂ σ y₀ k' x₀ = 0 := by simp only [eightSndTk, hg, ↓reduceIte]
    rw [hTk] at hle
    have hpos : (0 : ℝ) < eightS₁ x W₁ ζ₁ k x₀ := (hR1 k x₀).2
    exact absurd (le_antisymm hle (zero_le (a := eightS₁ x W₁ ζ₁ k x₀)))
      (fun h => by rw [h] at hpos; exact lt_irrefl 0 hpos)

end Col

end InteractingSLE.ZhanGT4.A1ESnd
