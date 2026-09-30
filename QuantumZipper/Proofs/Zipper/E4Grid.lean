import QuantumZipper.Proofs.Zipper.E4GridMeas
import QuantumZipper.Proofs.LQG.RevCouplingReg

/-!
# E4-GRID (G3): E1-NU at the `x`-dependent dyadic time `dyUp n σ_ε(x)`

`handoff/E4-A.md` (G3), `handoff/E-PLAN-2.md` (node E4-GRID, statement `E4GridStmt` of
`handoff/E-PLAN-2-statements.lean.txt`).

**`e4_grid`** (unconditional; `hReg` is discharged by `RevCouplingReg.revCouplingBoundaryMeasureRegular`
and E1-TR by `E1.e1_tr`; main theorems in `E4GridMain`): with
`s ω x = dyUp n (sigEps (Vr κ T B ω) T₀ ε x)` (`sG`, cap `T₀ ≤ T`),

`E ∫_{[−δ,0]} 1{s < T₀, x live at s} Ψ(x, V^s, W⁰) Φ(coords (Y_s − m)) dν
  = E ∫_{[−δ,0]} 1{s < T₀, x live at s} Ψ(x, V^s, W⁰) E'[Φ(coords (targetField … s … x X'))] dν`.

Route (Sheffield, arXiv:1012.4797, proof of Lemma 5.6, pp. 66–68: the Palm formula at fixed times
is applied at dyadic approximations of the stopping time): decompose `{s < T}` by the finitely many
grid values `t_k = k/2ⁿ < T₀` (`decomp_pt`); on `{s = t_k}` (the measurable grid event of G1,
`gridSet`) apply E1-NU (`E1Nu.e1_nu_of_tr`) at `t = t_k` with `Ψ_k = Ψ · 1_{gridSet}` (`PsiK`);
the outer integral splits by G2 (`E4GridMeas`). The ε > 0 of the plan's statement is not needed.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E4Grid

open B2 E1 CoordsFull PalmNorm

/-- The grid time `dyUp n σ_ε(x)` for the driver `V = Vr κ T B ω`, entrance time capped at
`T₀` (the plan's `E4GridStmt` is `T₀ = T`; E4-LIM uses `T₀ < T`). -/
def sG {Ω : Type*} (κ T T₀ : ℝ) (B : ℝ≥0 → Ω → ℝ) (ε : ℝ) (n : ℕ) (ω : Ω) (x : ℝ) : ℝ :=
  dyUp n (sigEps (Vr κ T B ω) T₀ ε x)

/-- The test function localized to the grid event of `t_k`. -/
def PsiK (T ε : ℝ) (n k : ℕ) (Ψ : ℝ → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞) :
    ℝ → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞ :=
  fun x d => (gridSet T ε n k).indicator (fun q => Ψ q.1 q.2) (x, d)

theorem measurable_PsiK {T ε : ℝ} {n k : ℕ} {Ψ : ℝ → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞}
    (hΨ : Measurable (Function.uncurry Ψ)) : Measurable (Function.uncurry (PsiK T ε n k Ψ)) :=
  hΨ.indicator (measurableSet_gridSet T ε n k)

theorem fst_neg_of_mem_gridSet {T ε : ℝ} {n k : ℕ} {q : ℝ × ((ℝ≥0 → ℝ) × (ℝ≥0 → ℝ))}
    (h : q ∈ gridSet T ε n k) : q.1 < 0 := h.2.1.2.1

theorem tk_lt_iff (n k : ℕ) (T : ℝ) : k < ⌈(2 : ℝ) ^ n * T⌉₊ ↔ tk n k < T := by
  rw [Nat.lt_ceil, tk, div_lt_iff₀ (by positivity), mul_comm]

theorem tk_injective (n : ℕ) : Function.Injective (tk n) := fun k k' h => by
  unfold tk at h
  rwa [div_left_inj' (by positivity), Nat.cast_inj] at h

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T T₀ : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {ϖ : Measure ℂ} {ε : ℝ} {n : ℕ}
  {Ψ : ℝ → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞}

omit [IsProbabilityMeasure P] in
theorem mem_gridSet_Vr {ω : Ω} (hc : Continuous fun s => B s ω) (hT : 0 ≤ T) (hT₀ : 0 ≤ T₀)
    {x : ℝ}
    (hx : x ≤ 0) (k : ℕ) :
    (x, (Vstop κ T (tk n k) B ω, W0p κ T B ω)) ∈ gridSet T₀ ε n k ↔
      tk n k < T₀ ∧ sG κ T T₀ B ε n ω x = tk n k ∧ IsLive (Vr κ T B ω) (tk n k) x := by
  have hV : Continuous (Vr κ T B ω) := continuous_vrev (drive_continuous hc) T
  have hD1 : Continuous (Vstop κ T (tk n k) B ω) :=
    hV.comp (NNReal.continuous_coe.min continuous_const)
  exact mem_gridSet_iff hV (vrev_zero hT) hD1 (E1Nu.eqOn_Vr_stopDrive ω) hT₀ hx

omit [IsProbabilityMeasure P] in
/-- On the grid event the point is live, so the live indicator is redundant. -/
theorem liveInd_eq {ω : Ω} (hc : Continuous fun s => B s ω) (hT : 0 ≤ T) (hT₀ : 0 ≤ T₀)
    (k : ℕ)
    (W : ℝ → ℝ≥0∞) (x : ℝ) :
    {x | IsLive (Vr κ T B ω) (tk n k) x}.indicator
      (fun x => PsiK T₀ ε n k Ψ x (Vstop κ T (tk n k) B ω, W0p κ T B ω) * W x) x =
      PsiK T₀ ε n k Ψ x (Vstop κ T (tk n k) B ω, W0p κ T B ω) * W x := by
  by_cases hl : IsLive (Vr κ T B ω) (tk n k) x
  · exact indicator_of_mem (show x ∈ {x | IsLive (Vr κ T B ω) (tk n k) x} from hl) _
  · rw [indicator_of_notMem (show x ∉ {x | IsLive (Vr κ T B ω) (tk n k) x} from hl)]
    by_cases h : (x, (Vstop κ T (tk n k) B ω, W0p κ T B ω)) ∈ gridSet T₀ ε n k
    · exact absurd ((mem_gridSet_Vr hc hT hT₀ (fst_neg_of_mem_gridSet h).le k).1 h).2.2 hl
    · rw [show PsiK T₀ ε n k Ψ x (Vstop κ T (tk n k) B ω, W0p κ T B ω) = 0 from
        indicator_of_notMem h _, zero_mul]

open Classical in
omit [IsProbabilityMeasure P] in
/-- **Pointwise grid decomposition.** -/
theorem decomp_pt {ω : Ω} (hc : Continuous fun s => B s ω) (hT : 0 ≤ T) (hT₀ : 0 < T₀)
    (Z : ℝ → ℝ → ℝ≥0∞)
    {x : ℝ} (hx : x ≤ 0) :
    {x | sG κ T T₀ B ε n ω x < T₀ ∧ IsLive (Vr κ T B ω) (sG κ T T₀ B ε n ω x) x}.indicator
      (fun x => Ψ x (Vstop κ T (sG κ T T₀ B ε n ω x) B ω, W0p κ T B ω) *
        Z x (sG κ T T₀ B ε n ω x)) x =
      ∑ k ∈ Finset.range ⌈(2 : ℝ) ^ n * T₀⌉₊, {x | IsLive (Vr κ T B ω) (tk n k) x}.indicator
        (fun x => PsiK T₀ ε n k Ψ x (Vstop κ T (tk n k) B ω, W0p κ T B ω) * Z x (tk n k)) x := by
  have hmem := fun k => mem_gridSet_Vr (ε := ε) (n := n) (κ := κ) hc hT hT₀.le hx k
  have hterm : ∀ k, {x | IsLive (Vr κ T B ω) (tk n k) x}.indicator
      (fun x => PsiK T₀ ε n k Ψ x (Vstop κ T (tk n k) B ω, W0p κ T B ω) * Z x (tk n k)) x =
      if (x, (Vstop κ T (tk n k) B ω, W0p κ T B ω)) ∈ gridSet T₀ ε n k then
        Ψ x (Vstop κ T (tk n k) B ω, W0p κ T B ω) * Z x (tk n k) else 0 := fun k => by
    rw [liveInd_eq hc hT hT₀.le k (fun x => Z x (tk n k)) x]
    unfold PsiK
    split_ifs with h
    · rw [indicator_of_mem h]
    · rw [indicator_of_notMem h, zero_mul]
  simp_rw [hterm]
  by_cases hev : sG κ T T₀ B ε n ω x < T₀ ∧ IsLive (Vr κ T B ω) (sG κ T T₀ B ε n ω x) x
  · have hσ : 0 ≤ (2 : ℝ) ^ n * sigEps (Vr κ T B ω) T₀ ε x :=
      mul_nonneg (by positivity) (sigEps_nonneg hT₀.le)
    set k0 := (⌈(2 : ℝ) ^ n * sigEps (Vr κ T B ω) T₀ ε x⌉).toNat with hk0def
    have hs : sG κ T T₀ B ε n ω x = tk n k0 := by
      rw [sG, dyUp, tk, hk0def]
      congr 1
      rw [show (((⌈(2 : ℝ) ^ n * sigEps (Vr κ T B ω) T₀ ε x⌉).toNat : ℕ) : ℝ) =
        (((⌈(2 : ℝ) ^ n * sigEps (Vr κ T B ω) T₀ ε x⌉).toNat : ℤ) : ℝ) by norm_cast,
        Int.toNat_of_nonneg (Int.ceil_nonneg hσ)]
    have hk0 : (x, (Vstop κ T (tk n k0) B ω, W0p κ T B ω)) ∈ gridSet T₀ ε n k0 :=
      (hmem k0).2 ⟨hs ▸ hev.1, hs, hs ▸ hev.2⟩
    rw [indicator_of_mem (show x ∈ {x | sG κ T T₀ B ε n ω x < T₀ ∧ IsLive (Vr κ T B ω) (sG κ T T₀ B ε n ω x) x} from hev), Finset.sum_eq_single k0]
    · rw [if_pos hk0, hs]
    · intro k _ hk
      rw [if_neg]
      intro h
      exact hk (tk_injective n (((hmem k).1 h).2.1.symm.trans hs))
    · intro hk
      exact absurd (Finset.mem_range.2 ((tk_lt_iff n k0 T₀).2 (hs ▸ hev.1))) hk
  · rw [indicator_of_notMem (show x ∉ {x | sG κ T T₀ B ε n ω x < T₀ ∧ IsLive (Vr κ T B ω) (sG κ T T₀ B ε n ω x) x} from hev)]
    symm
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [if_neg]
    intro h
    obtain ⟨h1, h2, h3⟩ := (hmem k).1 h
    exact hev ⟨h2 ▸ h1, h2 ▸ h3⟩

omit [IsProbabilityMeasure P] in
/-- **Integrated grid decomposition.** -/
theorem grid_lintegral (hT : 0 ≤ T) (hT₀ : 0 < T₀) (hB : IsBrownianReal B P) (δ : ℝ)
    (Z : Ω → ℝ → ℝ → ℝ≥0∞)
    (hmeas : ∀ᵐ ω ∂P, ∀ k ∈ Finset.range ⌈(2 : ℝ) ^ n * T₀⌉₊, Measurable fun x =>
      PsiK T₀ ε n k Ψ x (Vstop κ T (tk n k) B ω, W0p κ T B ω) * Z ω x (tk n k))
    (haem : ∀ k ∈ Finset.range ⌈(2 : ℝ) ^ n * T₀⌉₊, AEMeasurable (fun ω =>
      ∫⁻ x in Icc (-δ) 0, {x | IsLive (Vr κ T B ω) (tk n k) x}.indicator (fun x =>
        PsiK T₀ ε n k Ψ x (Vstop κ T (tk n k) B ω, W0p κ T B ω) * Z ω x (tk n k)) x
        ∂nuPalm κ T B X ϖ ω) P) :
    ∫⁻ ω, ∫⁻ x in Icc (-δ) 0,
        {x | sG κ T T₀ B ε n ω x < T₀ ∧ IsLive (Vr κ T B ω) (sG κ T T₀ B ε n ω x) x}.indicator
          (fun x => Ψ x (Vstop κ T (sG κ T T₀ B ε n ω x) B ω, W0p κ T B ω) *
            Z ω x (sG κ T T₀ B ε n ω x)) x ∂nuPalm κ T B X ϖ ω ∂P =
      ∑ k ∈ Finset.range ⌈(2 : ℝ) ^ n * T₀⌉₊, ∫⁻ ω, ∫⁻ x in Icc (-δ) 0,
        {x | IsLive (Vr κ T B ω) (tk n k) x}.indicator (fun x =>
          PsiK T₀ ε n k Ψ x (Vstop κ T (tk n k) B ω, W0p κ T B ω) * Z ω x (tk n k)) x
        ∂nuPalm κ T B X ϖ ω ∂P := by
  rw [← lintegral_finsetSum' _ haem]
  refine lintegral_congr_ae ?_
  filter_upwards [hB.cont, hmeas] with ω hc hm
  have hm' : ∀ k ∈ Finset.range ⌈(2 : ℝ) ^ n * T₀⌉₊, Measurable fun x =>
      {x | IsLive (Vr κ T B ω) (tk n k) x}.indicator (fun x =>
        PsiK T₀ ε n k Ψ x (Vstop κ T (tk n k) B ω, W0p κ T B ω) * Z ω x (tk n k)) x :=
    fun k hk => by
      simp_rw [liveInd_eq hc hT hT₀.le k (fun x => Z ω x (tk n k))]
      exact hm k hk
  rw [← lintegral_finsetSum _ hm']
  exact setLIntegral_congr_fun measurableSet_Icc fun x hx => decomp_pt hc hT hT₀ (Z ω) hx.2

end E4Grid
end QuantumZipper
