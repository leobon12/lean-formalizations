/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFin2Protected
import InteractingSLE.Spec.ZhanGT4.DualSeedFin3Axis
import InteractingSLE.Spec.ZhanGT4.A1PatchSeed

/-!
# Zhan's A.1 (R80): the two-sided bound (D9) of the seeded field, uniformly in both paths

Packet PROVE-A1-SEEDFIELD. Source: Astra, *Follow-up proofs*, §A.1.3 (`ig1_followup_proofs.txt` L300–L345: "There are
deterministic constants `0 < c < C < ∞`, depending on the enclosures and original marked configuration, such that
`c ≤ M(s, t) ≤ C` (`0 ≤ s ≤ S₁`, `0 ≤ t ≤ S₂`)", (D9)) and follow-up 4 §2.5 item 1 (L755–L762: "all the displayed
factors are continuous and bounded above and below by positive deterministic constants, even as an own seed gap tends
to zero. Together with the nondegenerate factors this proves exactly the two-sided bound (D9) for the seed density").

`IsRectField.bound` asks for ONE pair of constants for all samples of both curves. A22's `seeded_source_calculus_right`
proves a bound for each frozen sample separately (its constant is existentially quantified after the frozen path).
Its two enclosure lemmas, however, choose their constants before every path and time
(`exists_seed_remoteScale_right`, `exists_abs_normEll_le_right_of_remote_scale`); combining them gives the uniform
bound here.

## Main results

* **`exists_abs_normEll_le_uniform_right`**: one constant `K` bounds `|normEll|` of every seeded record built from the
  source (`SeedData.fromSource`) by a protected pair of enclosures, for all growing drivers, frozen paths, frozen
  heights `0 < t₂ ≤ Tm`, horizons `T ≤ Tm` and own times `t ≤ T`;
* **`seedHeightField_bound_of_abs`**: a uniform bound on the normalized logarithm gives the two-sided bound (D9) of the
  seeded height field (`IsRectField.bound`);
* `abs_normEll_sub_le_of_identity`: the zero-height record (identity chart) contributes nothing.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4.A1SeedField

open QuantumZipper (H fwdMap fwdHull)

/-- **The seeded logarithm is bounded uniformly in both paths** (§A.1.3, (D9); follow-up 4 §2.5 item 1): for a
protected pair of enclosures `H₁ ∋ 0`, `H₂ ∋ p` (separation `2δ`, a protected point `q ∈ (0, p)`), one constant `K`
bounds `|normEll t|` of the source record (`SeedData.fromSource`) of every growing driver `W` whose hull stays in `H₁`
up to `T ≤ Tm`, with seed coordinates between the two outermost seeds `Vlo`, `Vhi`, for every frozen path `W₂` from `p`
whose hull at the frozen height `0 < t₂ ≤ Tm` stays in `H₂`, and every own time `t ≤ T`. -/
theorem exists_abs_normEll_le_uniform_right {H₁ H₂ : Set ℂ}
    (hH₁ : IsHPHull H₁) (hH₂ : IsHPHull H₂) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ a ∈ H₂, ∀ z ∈ H₁, 2 * δ ≤ ‖a - z‖)
    {p q d : ℝ} (hpH₂ : (p : ℂ) ∈ closure H₂) (hq : 0 < q) (hqp : q < p)
    (hd : 0 < d) (hqH : Disjoint (ball (q : ℂ) (2 * d)) (H₁ ∪ H₂)) (Tm κ : ℝ) {n : ℕ} (rr : Fin n → ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (W W₂ a W' Vlo Vhi : ℝ → ℝ) (V : Fin n → ℝ → ℝ) (T t₂ : ℝ),
        OwnData W (fwdHull W₂ t₂) (fun z => fwdMap W₂ t₂ z + W₂ t₂) T a W' →
        Continuous W₂ → W₂ 0 = p → 0 < t₂ → t₂ ≤ Tm → T ≤ Tm →
        fwdHull W T ⊆ H₁ → fwdHull W₂ t₂ ⊆ H₂ →
        IsSeedCoordinate W Vlo T → IsSeedCoordinate W Vhi T →
        (∀ t ∈ Icc (0 : ℝ) T, W t ∈ uIcc (Vlo t) (Vhi t)) →
        (∀ t ∈ Icc (0 : ℝ) T, ∀ m, V m t ∈ uIcc (Vlo t) (Vhi t)) →
        ∀ t ∈ Icc (0 : ℝ) T,
          |(SeedData.fromSource W W' a (fun z => fwdMap W₂ t₂ z + W₂ t₂) κ rr (W₂ t₂) p V).normEll t| ≤ K := by
  obtain ⟨Lrem, -, hrem⟩ := exists_seed_remoteScale_right hH₁ hH₂ hδ hsep hpH₂ hq hqp hd hqH Tm
  obtain ⟨r, L, -, hL, hb⟩ :=
    exists_abs_normEll_le_right_of_remote_scale hH₁ hH₂ hδ hsep hd hqH Tm Lrem κ rr
  have hcoef : 0 ≤ coefTot κ rr := by
    unfold coefTot
    have h1 : 0 ≤ ∑ m, (|rr m| + |dualGamma κ (rr m)| + |κ / 4 * rr m|) :=
      Finset.sum_nonneg fun m _ => by positivity
    have h2 : 0 ≤ pairSum (fun m k => |dualDelta κ (rr m) (rr k)|) :=
      pairSum_nonneg fun m k => abs_nonneg _
    positivity
  refine ⟨coefTot κ rr * L, mul_nonneg hcoef hL, ?_⟩
  intro W W₂ a W' Vlo Vhi V T t₂ h hW₂ hW₂0 ht₂ ht₂m hTm hK₁ hK₂ hlo hhi hWI hVI t ht
  have hW0H : ((W 0 : ℝ) : ℂ) ∈ closure H₁ := closure_mono hK₁ (start_mem_closure_fwdHull h.cont h.pos)
  have hW₂H : ((W₂ 0 : ℝ) : ℂ) ∈ closure H₂ := by rw [hW₂0]; exact hpH₂
  have hWq : W 0 < q := by rw [h.zero]; exact hq
  have hqW : q < W₂ 0 := by rw [hW₂0]; exact hqp
  have hremote := hrem κ rr W W₂ a W' Vlo Vhi V T t₂ h hW₂ hW₂0 ht₂ ht₂m hTm hK₁ hK₂ hlo hhi hWI hVI
  exact hb (SeedData.fromSource W W' a (fun z => fwdMap W₂ t₂ z + W₂ t₂) κ rr (W₂ t₂) p V) W₂ Vlo Vhi T t₂ h rfl
    rfl rfl hW₂ ht₂ ht₂m hW0H hW₂H hWq hqW hK₁ hK₂ hlo hhi hWI hVI hremote t ht

/-- The difference of two values of a logarithm bounded by `K` is bounded by `2K`. -/
theorem abs_normEll_sub_le {n : ℕ} {s : SeedData n} {K u v : ℝ} (hu : |s.normEll u| ≤ K)
    (hv : |s.normEll v| ≤ K) : |s.normEll u - s.normEll v| ≤ 2 * K := by
  calc |s.normEll u - s.normEll v| ≤ |s.normEll u| + |s.normEll v| := abs_sub _ _
    _ ≤ 2 * K := by linarith

/-- **The zero-height record contributes nothing**: in an identity chart (the factor identities of
`SeedData.normEll_eq_zero_of_identity` at the two times) the normalized logarithm has equal values. -/
theorem abs_normEll_sub_le_of_identity {n : ℕ} (s : SeedData n) {u : ℝ}
    (hf : ∀ t, s.F 0 t = id) (hA : ∀ t, s.A 1 t = 1) (h21 : ∀ t, s.A21 t = 1)
    (hB : ∀ t m, s.B1 t m = 1) (h20 : ∀ t, s.A20 t = s.V₀ t) (hL : ∀ t, s.L t = 0) {K : ℝ} (hK : 0 ≤ K) :
    |s.normEll u - s.normEll 0| ≤ K := by
  rw [s.normEll_eq_zero_of_identity u (hf u) (hA u) (h21 u) (hB u) (h20 u) (hL u),
    s.normEll_eq_zero_of_identity 0 (hf 0) (hA 0) (h21 0) (hB 0) (h20 0) (hL 0), sub_self, abs_zero]
  exact hK

section Field

variable {X Y : Type*} {n : ℕ}

/-- **The two-sided bound (D9) of the seeded height field** from a uniform bound on the normalized logarithm: if
`|normEll s − normEll 0| ≤ K` for every record of the rectangle, then `exp (−K) ≤ N ≤ exp K` there. This is
`IsRectField.bound` for `seedHeightField d`. -/
theorem seedHeightField_bound_of_abs {d : ℝ → X × Y → SeedData n} {S₁ : X → ℝ≥0} {S₂ : Y → ℝ≥0} {K : ℝ}
    (hK : ∀ x y (s t : ℝ), 0 ≤ s → s ≤ S₁ x → 0 ≤ t → t ≤ S₂ y →
      |(d t (x, y)).normEll s - (d t (x, y)).normEll 0| ≤ K) :
    ∃ c C : ℝ, 0 < c ∧ ∀ x y (s t : ℝ), 0 ≤ s → s ≤ S₁ x → 0 ≤ t → t ≤ S₂ y →
      c ≤ seedHeightField d (x, y) s t ∧ seedHeightField d (x, y) s t ≤ C := by
  refine ⟨Real.exp (-K), Real.exp K, Real.exp_pos _, fun x y s t hs hsS ht htS => ?_⟩
  have h := abs_le.1 (hK x y s t hs hsS ht htS)
  exact ⟨Real.exp_le_exp.2 h.1, Real.exp_le_exp.2 h.2⟩

/-- **(D9) from the uniform seeded bound**: positive frozen heights by `exists_abs_normEll_le_uniform_right` (each
record bounded by `K`, so the normalized difference by `2K`), the zero height by the identity chart. -/
theorem seedHeightField_bound_of_pos_zero {d : ℝ → X × Y → SeedData n} {S₁ : X → ℝ≥0} {S₂ : Y → ℝ≥0} {K : ℝ}
    (hK0 : 0 ≤ K)
    (hpos : ∀ x y (s t : ℝ), 0 ≤ s → s ≤ S₁ x → 0 < t → t ≤ S₂ y →
      |(d t (x, y)).normEll s| ≤ K ∧ |(d t (x, y)).normEll 0| ≤ K)
    (hzero : ∀ x y (s : ℝ), 0 ≤ s → s ≤ S₁ x → (d 0 (x, y)).normEll s = (d 0 (x, y)).normEll 0) :
    ∃ c C : ℝ, 0 < c ∧ ∀ x y (s t : ℝ), 0 ≤ s → s ≤ S₁ x → 0 ≤ t → t ≤ S₂ y →
      c ≤ seedHeightField d (x, y) s t ∧ seedHeightField d (x, y) s t ≤ C := by
  refine seedHeightField_bound_of_abs (K := 2 * K) fun x y s t hs hsS ht htS => ?_
  rcases ht.eq_or_lt with rfl | ht0
  · rw [hzero x y s hs hsS, sub_self, abs_zero]
    positivity
  · exact abs_normEll_sub_le (hpos x y s t hs hsS ht0 htS).1 (hpos x y s t hs hsS ht0 htS).2

end Field

end InteractingSLE.ZhanGT4.A1SeedField
