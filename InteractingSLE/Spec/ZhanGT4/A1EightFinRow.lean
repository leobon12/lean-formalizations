/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1EightFinGap
import InteractingSLE.Spec.ZhanGT4.DualSeedFusedOriginal

/-!
# Zhan's A.1 (Eight): the row martingales from A22's fused-density martingale

Packet PROVE-A1-EIGHTFIN. Source: Astra, *Follow-up proofs*, §A.1.4 (`ig1_followup_proofs.txt` L363–L407: "with the
first path fixed, `t ↦ M(s, t)` is a martingale in the second filtration") and follow-up 4 §2.5 (L739–L788).

Fix the small curve (driver `W₁` up to its horizon `S`, seeds `Vlo`, `Vhi`) and a positive own time `a ≤ S`. The
row of the seeded field is `t ↦ exp(d_t.normEll a − d_t.normEll 0)` along the large curve, `d_t` the column records
at height `t ∧ S₂`. By `normEll_srcRec_sub_eq_eView` it is A22's fused normalized density
`FrzData.seedAccessDensity` of the opposite view `eView … a`; A22's `seedAccess_density_facts` makes the latter a
continuous bounded martingale. Its remaining inputs are discharged here: the (D9) constants (`ViewSetup.d9_eView`
with `exists_colBounds`, `exists_clr_eView`), the source gap (`exists_real_gap_bounds`), aliveness of the opposite
tip and of the seed accesses, and the vanishing fused exponent. What is left is the stochastic half of the row:

* `IsRowStoch`: the large curve's driving Brownian motion (continuous at every sample), its continuous adapted drift
  part (constant on the horizon: the fused exponent vanishes), and the adapted source coordinate of a protected real
  point `x₀`;
* **`row_martingale`**: the row is a martingale with continuous paths.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4.A1EightFin

open QuantumZipper (H IsForwardSol fwdMap fwdHull)
open A1SeedField A1EightSeed

/-! ### The vanishing fused exponent -/

/-- With vanishing fused exponent the fused log density is the raw one. -/
theorem seedAccessEll_eq_ell {n : ℕ} (d : FrzData n) (h0 : d.seedAccessExponent = 0) (p t x : ℝ) :
    d.seedAccessEll p t x = d.ell t x := by
  simp only [FrzData.seedAccessEll, h0, dualGamma_zero, zero_mul, sub_zero]

/-- The opposite view's fused exponent is the column charges' fused exponent. -/
theorem seedAccessExponent_eView {n : ℕ} (κ : ℝ) (rr : Fin n → ℝ) (W₁ V₂ : ℝ → ℝ) (S Y : ℝ) (V : Fin n → ℝ → ℝ)
    (a : ℝ) : (eView κ rr W₁ V₂ S Y V a).seedAccessExponent = -1 / 2 + ∑ m, -(κ / 4) * rr m := rfl

/-! ### The stochastic half of a row -/

section Stoch

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The stochastic half of a row** (the large curve's analogue of A1-EIGHTSEED's `IsColumnStoch`): `B` is an
`𝓕`-Brownian motion with continuous paths, `D` is adapted and continuous, the opposite drivers are `√κ B + D`, `D` is
constant on the horizon (zero force drift), and `V` is an adapted process equal on the horizon to the source
coordinate `Re g_u(x₀) + W_u` of the real point `x₀`. -/
def IsRowStoch (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (κ : ℝ) (Wd : Ω → ℝ → ℝ) (S : Ω → ℝ≥0) (x₀ : ℝ)
    (B D : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ → ℝ) : Prop :=
  IsFilteredBrownianReal 𝓕 B P ∧ (∀ ω, Continuous (B · ω)) ∧ (∀ u, Measurable[𝓕 u] (D u)) ∧
    (∀ ω, Continuous (D · ω)) ∧ (∀ ω, Wd ω = driftDriver (Real.sqrt κ) B D ω) ∧
    (∀ ω, ∀ t ∈ Icc (0 : ℝ) (S ω), HasDerivWithinAt (fun s : ℝ => D s.toNNReal ω) 0 (Icc (0 : ℝ) (S ω)) t) ∧
    (∀ u : ℝ≥0, Measurable[𝓕 u] fun ω => V ω u) ∧
    ∀ ω, ∀ u ∈ Icc (0 : ℝ) (S ω), V ω u = (fwdMap (Wd ω) u x₀).re + Wd ω u

end Stoch

/-! ### The row martingale -/

/-- The two seeds, distinct at a time, give an injective mark family. -/
theorem pair_injective {Vlo Vhi : ℝ → ℝ} {u : ℝ} (h : Vlo u ≠ Vhi u) :
    Function.Injective fun m : Fin 2 => ![Vlo, Vhi] m u := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exact absurd hij h
  · exact absurd hij.symm h
  · rfl

section Row

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The row martingale** (Eight, vanishing fused exponent): fix the small curve and a positive own time `a ≤ S`;
for every sample `ω` of the large curve let `ViewSetup` hold for the rectangle `[0, S] × [0, S₂ ω]` with the large
path `V₂ ω`. Given the stochastic half of the row (`IsRowStoch`, for a protected real point `x₀ < 0` left of the large
curve's enclosure), the row `t ↦ exp(d_{t∧S₂}.normEll a − d_{t∧S₂}.normEll 0)` of the column records is a martingale
with continuous paths. -/
theorem row_martingale {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {H₁ H₂ : Set ℂ} {δ p q dd Tm : ℝ} (hpp : IsProtectedPair H₁ H₂ δ p q dd)
    {κ : ℝ} (hκ : 0 < κ) {rr : Fin 2 → ℝ} (hE : -1 / 2 + ∑ m, -(κ / 4) * rr m = 0)
    {W₁ : ℝ → ℝ} {S : ℝ} {Vlo Vhi : ℝ → ℝ} {V₂ : Ω → ℝ → ℝ} {S₂ : Ω → ℝ≥0}
    (hset : ∀ ω, ViewSetup H₁ H₂ δ p q dd Tm W₁ (V₂ ω) S (S₂ ω) Vlo Vhi)
    (hS₂ : IsStoppingTime 𝓕 fun ω => (S₂ ω : WithTop ℝ≥0))
    {x₀ ρ : ℝ} (hρ : 0 < ρ) (hx₀ : x₀ < 0) (hx₀G : Disjoint (ball (x₀ : ℂ) ρ) (transl (-p) H₂))
    {B D : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ → ℝ}
    (hst : IsRowStoch 𝓕 P (16 / κ) (fun ω u => V₂ ω u - V₂ ω 0) S₂ x₀ B D V)
    {a : ℝ} (ha : a ∈ Ioc (0 : ℝ) S) :
    Martingale (fun (t : ℝ≥0) ω => Real.exp
        ((srcRec W₁ S (V₂ ω) (min (t : ℝ) (S₂ ω)) κ rr p ![Vlo, Vhi]).normEll a -
          (srcRec W₁ S (V₂ ω) (min (t : ℝ) (S₂ ω)) κ rr p ![Vlo, Vhi]).normEll 0)) 𝓕 P ∧
      ∀ ω, Continuous fun t : ℝ≥0 => Real.exp
        ((srcRec W₁ S (V₂ ω) (min (t : ℝ) (S₂ ω)) κ rr p ![Vlo, Vhi]).normEll a -
          (srcRec W₁ S (V₂ ω) (min (t : ℝ) (S₂ ω)) κ rr p ![Vlo, Vhi]).normEll 0) := by
  obtain ⟨hB, hBc, hDm, hDc, hdW, hD0, hVm, hV⟩ := hst
  have hκ0 : κ ≠ 0 := hκ.ne'
  have haI : a ∈ Icc (0 : ℝ) S := Ioc_subset_Icc_self ha
  obtain ⟨ω₀⟩ := nonempty_of_isProbabilityMeasure P
  set d : Ω → FrzData 2 := fun ω => eView κ rr W₁ (V₂ ω) S (S₂ ω) ![Vlo, Vhi] a with hd
  have hzero : ∀ ω, V₂ ω 0 = p := fun ω => (hset ω).zero₂
  have hexp : ∀ ω, (d ω).seedAccessExponent = 0 := fun ω => by rw [seedAccessExponent_eView, hE]
  have hVs : ∀ ω m, IsSeedCoordinate W₁ (![Vlo, Vhi] m) S := fun ω m => by
    fin_cases m
    · exact (hset ω).lo
    · exact (hset ω).hi
  -- the row is the opposite view's fused density
  have hrow : ∀ (t : ℝ≥0) ω, Real.exp
      ((srcRec W₁ S (V₂ ω) (min (t : ℝ) (S₂ ω)) κ rr p ![Vlo, Vhi]).normEll a -
        (srcRec W₁ S (V₂ ω) (min (t : ℝ) (S₂ ω)) κ rr p ![Vlo, Vhi]).normEll 0) =
      (d ω).seedAccessDensity x₀ (S₂ ω) t := by
    intro t ω
    have hmin : min (t : ℝ) (S₂ ω) ∈ Icc (0 : ℝ) (S₂ ω) :=
      ⟨le_min t.coe_nonneg (S₂ ω).coe_nonneg, min_le_right _ _⟩
    rw [(hset ω).normEll_srcRec_sub_eq_eView hκ0 hE (hVs ω) (fun u _ m => seedPair_marks Vlo Vhi u m)
      (fun u hu => pair_injective ((hset ω).inj u hu)) ha hmin]
    simp only [FrzData.seedAccessDensity, seedAccessEll_eq_ell _ (hexp ω)]
    rfl
  -- the uniform constants
  obtain ⟨L, hL0, hcb⟩ := exists_colBounds hpp Tm
  obtain ⟨r, hr, hclr⟩ := exists_clr_eView hpp Tm
  have hG : IsHPHull (transl (-p) H₂) := isHPHull_transl hpp.hull₂ (-p)
  obtain ⟨R, hR⟩ := hG.2.1.exists_norm_le
  set xr : ℝ := max R 0 + 2 with hxr
  have hxrG : Disjoint (ball (xr : ℂ) 1) (transl (-p) H₂) := by
    refine Set.disjoint_left.2 fun z hz hzG => ?_
    have h1 := hR z hzG
    rw [mem_ball, dist_eq_norm] at hz
    have h2 : ‖(xr : ℂ)‖ ≤ ‖z‖ + ‖z - xr‖ := by
      calc ‖(xr : ℂ)‖ = ‖z - (z - xr)‖ := by ring_nf
        _ ≤ ‖z‖ + ‖z - xr‖ := norm_sub_le _ _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at h2
    linarith [le_max_left R 0]
  have hxr0 : 0 < xr := by positivity
  obtain ⟨c₀, C₀, hc₀, hC₀, hgapb⟩ := exists_real_gap_bounds hG (lt_min hρ one_pos)
    (hx₀G.mono_left (ball_subset_ball (min_le_left _ _))) (hxrG.mono_left (ball_subset_ball (min_le_right _ _))) Tm
  set a₀ := Real.exp (-L) * (deriv (fwdMap W₁ a) p).re with ha₀def
  set γ := Real.exp (-L) * gapMin (W₁ a) ((fwdMap W₁ a p).re + W₁ a) (Vlo a) (Vhi a) with hγdef
  set Γ := Real.exp L * gapSum (W₁ a) ((fwdMap W₁ a p).re + W₁ a) (Vlo a) (Vhi a) with hΓdef
  have ha₀ : 0 < a₀ := mul_pos (Real.exp_pos _) ((hset ω₀).srcDeriv_pos haI)
  have hγ : 0 < γ := mul_pos (Real.exp_pos _) ((hset ω₀).gapMin_pos ha)
  obtain ⟨Lsc, hLsc⟩ := exists_scaleOK hr ha₀ hγ Γ L Tm
  set A := fwdHull (fun u => W₁ u - p) a with hA
  have eA : ∀ ω, fwdHull (fun u => W₁ u - V₂ ω 0) a = A := fun ω => by rw [hzero ω]
  have hWc : ∀ ω, Continuous (d ω).W := fun ω => (hset ω).cont₂.sub continuous_const
  have hK : ∀ ω, fwdHull (d ω).W (S₂ ω) ⊆ transl (-p) H₂ := fun ω => by
    have := fwdHull_sub_const_subset (c := V₂ ω 0) (hset ω).K₂
    change fwdHull (fun u => V₂ ω u - V₂ ω 0) (S₂ ω) ⊆ _
    rw [hzero ω] at this ⊢
    exact this
  have hW0 : ∀ ω, (((d ω).W 0 : ℝ) : ℂ) ∈ closure (transl (-p) H₂) := fun ω => by
    have := mem_closure_transl hpp.src (-p)
    change (((V₂ ω 0 - V₂ ω 0 : ℝ)) : ℂ) ∈ _
    simpa only [sub_self, ofReal_zero, ofReal_neg, add_neg_cancel] using this
  have hd0 : ∀ ω, (d ω).W 0 = 0 := fun ω => sub_self _
  obtain ⟨hmart, hcont, -, -⟩ := seedAccess_density_facts (P := P) (by positivity : 0 < 16 / κ)
    (fun m => -(κ / 4) * rr m) 𝓕 B D S₂ d (A := A) (φ := frzChart (fun u => W₁ u - p) a) (ζ₀ := W₁ a - p)
    (p := x₀) (ζ := fun m => ![Vlo, Vhi] m a - p) (V := V)
    hdW (fun _ => rfl) (fun _ => rfl)
    (fun ω => by change frzChart (fun u => W₁ u - V₂ ω 0) a = _; rw [hzero ω])
    (fun ω => by change W₁ a - V₂ ω 0 = _; rw [hzero ω])
    (fun ω => by change (fun m => ![Vlo, Vhi] m a - V₂ ω 0) = _; rw [hzero ω])
    hB hDm hBc hDc hVm hV hS₂ hr ha₀ hγ hc₀ hC₀ hLsc (fun ω => (hset ω).le₂)
    (fun ω => by
      have := ((hset ω).tOwn haI).1
      rw [eA ω] at this
      exact this)
    (fun ω => by
      have := (hset ω).d9_eView rr hr ha (fun t ht => hcb κ rr W₁ (V₂ ω) S (S₂ ω) Vlo Vhi (hset ω) t ht a haI)
        (fun t ht => hclr W₁ (V₂ ω) S (S₂ ω) Vlo Vhi (hset ω) a haI t ht)
      rw [eA ω] at this
      exact this)
    (fun ω => ((hset ω).tOwn haI).2)
    (fun ω m => by
      obtain ⟨qv, hqv, -⟩ := (hset ω).seed_access haI (seedPair_marks Vlo Vhi a m)
      exact ⟨qv, hqv⟩)
    (fun ω m => by
      change ![Vlo, Vhi] m a - V₂ ω 0 ≠ W₁ a - V₂ ω 0
      intro he
      exact (hVs ω m).ne a ha (by linarith))
    (fun ω => by
      intro i j hij
      exact pair_injective ((hset ω).inj a ha) (sub_left_injective hij))
    (fun ω => exists_isForwardSol_of_disjoint_ball_gen (hWc ω) (by rw [hd0 ω]; exact hx₀.ne) (S₂ ω).coe_nonneg hρ
      (hx₀G.mono_right (hK ω)))
    (fun ω t ht => hgapb (d ω).W (hWc ω) (hW0 ω) (by rw [hd0 ω]; exact hx₀) (by rw [hd0 ω]; exact hxr0) (S₂ ω)
      (S₂ ω).coe_nonneg (hset ω).le₂ (hK ω) t ht)
    (fun ω t ht => by
      rw [hexp ω, mul_zero, zero_div]
      exact hD0 ω t ht)
  refine ⟨?_, fun ω => ?_⟩
  · have e : (fun (t : ℝ≥0) ω => Real.exp
        ((srcRec W₁ S (V₂ ω) (min (t : ℝ) (S₂ ω)) κ rr p ![Vlo, Vhi]).normEll a -
          (srcRec W₁ S (V₂ ω) (min (t : ℝ) (S₂ ω)) κ rr p ![Vlo, Vhi]).normEll 0)) =
        fun t ω => (d ω).seedAccessDensity x₀ (S₂ ω) t := funext₂ hrow
    rw [e]
    exact hmart
  · have e : (fun t : ℝ≥0 => Real.exp
        ((srcRec W₁ S (V₂ ω) (min (t : ℝ) (S₂ ω)) κ rr p ![Vlo, Vhi]).normEll a -
          (srcRec W₁ S (V₂ ω) (min (t : ℝ) (S₂ ω)) κ rr p ![Vlo, Vhi]).normEll 0)) =
        fun t => (d ω).seedAccessDensity x₀ (S₂ ω) t := funext fun t => hrow t ω
    rw [e]
    exact hcont ω

end Row

end InteractingSLE.ZhanGT4.A1EightFin
