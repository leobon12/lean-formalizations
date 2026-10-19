import GaussianLQG.LQG.Bridge.Basic
import GaussianLQG.LQG.Bridge.LFPPRotBdd

/-!
# Rotation covariance of the canonical γ-LQG metric

Blueprint Proposition `prop:metric-facts` (F3), rotation case: "it also follows directly from the
exact rotation covariance of LFPP and the convergence of `a_ε⁻¹ D^ε_h`, since `a_ε` is
deterministic". For a canonical γ-LQG metric `D` (`GaussianLQG.IsCanonicalLQGMetric`), a
whole-plane GFF plus a bounded continuous function `h` and `‖a‖ = 1`, almost surely

  `D_{h(a·)}(u, v) = D_h(a u, a v)` for all `u, v`

(`IsCanonicalLQGMetric.ae_rotDist_of_isGFFPlusBddCont`; for a whole-plane GFF, in particular a
normalized one, `IsCanonicalLQGMetric.ae_rotDist`), where `h(a·) = GaussianLQG.rotDist a h`.

Proof. By `GaussianLQG.ae_lfppDistE_rotDist_of_isGFFPlusBddCont`, for each `ε > 0`, almost
surely `D^ε_{h(a·)}(u, v) = D^ε_h(a u, a v)` for all `u, v`. Both `h` and `h(a·)` are whole-plane
GFFs plus bounded continuous functions, so `𝔞_ε⁻¹ D^ε_h → D_h` and `𝔞_ε⁻¹ D^ε_{h(a·)} → D_{h(a·)}`
in probability for the local uniform topology, with the same deterministic `𝔞_ε`. The rotation maps `B̄_R(0)²` into itself, so limits
in probability are a.s. unique up to the change of coordinates
(`ae_eq_comp_of_tendstoInProbLU`).

The same uniqueness of limits shows that two canonical γ-LQG metrics agree almost surely on every
whole-plane GFF plus a bounded continuous function (`IsCanonicalLQGMetric.ae_eq`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace GaussianLQG

open LQGMetric

/-! ## Uniqueness of limits in probability up to a change of coordinates -/

section Unique

variable {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} {l : Filter ι}
  {X X' : ι → Ω → ℂ × ℂ → ℝ} {Y Y' : Ω → ℂ × ℂ → ℝ} {T : ℂ × ℂ → ℂ × ℂ}

/-- the compact `B̄_R(0)²` of the local uniform topology -/
abbrev sqBall (R : ℝ) : Set (ℂ × ℂ) := closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R

omit [MeasurableSpace Ω] in
/-- One step: a pointwise discrepancy `2δ ≤ |Y' p − Y (T p)|` forces a discrepancy `δ` between
one of the approximations and its limit. -/
lemma mem_union_of_two_mul_le {R δ : ℝ} {i : ι} {ω : Ω}
    (hT : ∀ p ∈ sqBall R, T p ∈ sqBall R) (hω : ∀ p, X' i ω p = X i ω (T p)) {p : ℂ × ℂ}
    (hp : p ∈ sqBall R) (hd : 2 * δ ≤ dist (Y' ω p) (Y ω (T p))) :
    ENNReal.ofReal δ ≤ ⨆ q ∈ sqBall R, edist (X' i ω q) (Y' ω q) ∨
      ENNReal.ofReal δ ≤ ⨆ q ∈ sqBall R, edist (X i ω q) (Y ω q) := by
  have htri : dist (Y' ω p) (Y ω (T p)) ≤
      dist (X' i ω p) (Y' ω p) + dist (X i ω (T p)) (Y ω (T p)) := by
    calc dist (Y' ω p) (Y ω (T p)) ≤ dist (Y' ω p) (X' i ω p) + dist (X' i ω p) (Y ω (T p)) :=
          dist_triangle _ _ _
      _ = dist (X' i ω p) (Y' ω p) + dist (X i ω (T p)) (Y ω (T p)) := by
          rw [dist_comm (Y' ω p), hω p]
  rcases le_or_gt δ (dist (X' i ω p) (Y' ω p)) with h1 | h1
  · left
    refine le_trans ?_ (le_iSup₂ (f := fun q _ => edist (X' i ω q) (Y' ω q)) p hp)
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal h1
  · right
    refine le_trans ?_ (le_iSup₂ (f := fun q _ => edist (X i ω q) (Y ω q)) (T p) (hT p hp))
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal (by linarith)

/-- For fixed `R, δ > 0`, the event `{∃ p ∈ B̄_R(0)², 2δ ≤ |Y' p − Y (T p)|}` is null. -/
lemma measure_discrepancy_eq_zero [l.NeBot] (hT : ∀ R, ∀ p ∈ sqBall R, T p ∈ sqBall R)
    (hX : TendstoInProbLU P X l Y) (hX' : TendstoInProbLU P X' l Y')
    (hXX' : ∀ᶠ i in l, ∀ᵐ ω ∂P, ∀ p, X' i ω p = X i ω (T p)) {R δ : ℝ} (hR : 0 < R)
    (hδ : 0 < δ) :
    P {ω | ∃ p ∈ sqBall R, 2 * δ ≤ dist (Y' ω p) (Y ω (T p))} = 0 := by
  set A := {ω | ∃ p ∈ sqBall R, 2 * δ ≤ dist (Y' ω p) (Y ω (T p))}
  set B' : ι → Set Ω := fun i =>
    {ω | ENNReal.ofReal δ ≤ ⨆ q ∈ sqBall R, edist (X' i ω q) (Y' ω q)}
  set B : ι → Set Ω := fun i =>
    {ω | ENNReal.ofReal δ ≤ ⨆ q ∈ sqBall R, edist (X i ω q) (Y ω q)}
  have hle : ∀ᶠ i in l, P A ≤ P (B' i) + P (B i) := by
    filter_upwards [hXX'] with i hi
    set N := {ω | ¬ ∀ p, X' i ω p = X i ω (T p)}
    have hN : P N = 0 := ae_iff.1 hi
    have hsub : A ⊆ (B' i ∪ B i) ∪ N := by
      rintro ω ⟨p, hp, hd⟩
      by_cases hω : ∀ p, X' i ω p = X i ω (T p)
      · left
        exact mem_union_of_two_mul_le (hT R) hω hp hd
      · right
        exact hω
    calc P A ≤ P ((B' i ∪ B i) ∪ N) := measure_mono hsub
      _ ≤ P (B' i ∪ B i) + P N := measure_union_le _ _
      _ = P (B' i ∪ B i) := by rw [hN, add_zero]
      _ ≤ P (B' i) + P (B i) := measure_union_le _ _
  have hlim : Tendsto (fun i => P (B' i) + P (B i)) l (𝓝 0) := by
    have := (hX' R hR δ hδ).add (hX R hR δ hδ)
    rwa [add_zero] at this
  exact nonpos_iff_eq_zero.1 (ge_of_tendsto hlim hle)

/-- **Uniqueness of limits in probability up to a change of coordinates.** If
`X → Y` and `X' → Y'` in probability for the local uniform topology, the map `T` sends each
`B̄_R(0)²` into itself, and eventually `X' i = X i ∘ T` almost surely, then almost surely
`Y' = Y ∘ T`. -/
theorem ae_eq_comp_of_tendstoInProbLU [l.NeBot] (hT : ∀ R, ∀ p ∈ sqBall R, T p ∈ sqBall R)
    (hX : TendstoInProbLU P X l Y) (hX' : TendstoInProbLU P X' l Y')
    (hXX' : ∀ᶠ i in l, ∀ᵐ ω ∂P, ∀ p, X' i ω p = X i ω (T p)) :
    ∀ᵐ ω ∂P, ∀ p, Y' ω p = Y ω (T p) := by
  set A : ℕ → Set Ω := fun n => {ω | ∃ p ∈ sqBall ((n : ℝ) + 1),
    2 * (2 * ((n : ℝ) + 1))⁻¹ ≤ dist (Y' ω p) (Y ω (T p))}
  have hA : ∀ n, P (A n) = 0 := fun n =>
    measure_discrepancy_eq_zero hT hX hX' hXX' (by positivity) (by positivity)
  refine ae_iff.2 (measure_mono_null (fun ω hω => ?_) (measure_iUnion_null hA))
  simp only [mem_ofPred_eq, not_forall] at hω
  obtain ⟨p, hp⟩ := hω
  have hd : 0 < dist (Y' ω p) (Y ω (T p)) := dist_pos.2 hp
  obtain ⟨n, hn⟩ := exists_nat_ge (max (max ‖p.1‖ ‖p.2‖) (dist (Y' ω p) (Y ω (T p)))⁻¹)
  have h1 : max ‖p.1‖ ‖p.2‖ ≤ n := (le_max_left _ _).trans hn
  have h2 : (dist (Y' ω p) (Y ω (T p)))⁻¹ ≤ n := (le_max_right _ _).trans hn
  refine mem_iUnion.2 ⟨n, p, ⟨?_, ?_⟩, ?_⟩
  · rw [mem_closedBall_zero_iff]
    linarith [le_max_left ‖p.1‖ ‖p.2‖]
  · rw [mem_closedBall_zero_iff]
    linarith [le_max_right ‖p.1‖ ‖p.2‖]
  · have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have e : 2 * (2 * ((n : ℝ) + 1))⁻¹ = ((n : ℝ) + 1)⁻¹ := by
      field_simp
    rw [e]
    have h3 : (dist (Y' ω p) (Y ω (T p)))⁻¹ ≤ (n : ℝ) + 1 := by linarith
    have := inv_anti₀ (inv_pos.2 hd) h3
    rwa [inv_inv] at this

end Unique

/-- **The canonical γ-LQG metric is almost surely unique**: two canonical γ-LQG metrics agree
almost surely on every whole-plane GFF plus a bounded continuous function (both are the limit in
probability of the same `𝔞_ε⁻¹ D^ε_h`). -/
theorem IsCanonicalLQGMetric.ae_eq {γ : ℝ} {D D' : DistC → ContMetric}
    (hD : IsCanonicalLQGMetric γ D) (hD' : IsCanonicalLQGMetric γ D') {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsGFFPlusBddCont h P) : ∀ᵐ ω ∂P, D (h ω) = D' (h ω) := by
  have key := ae_eq_comp_of_tendstoInProbLU (T := id) (fun _ _ hp => hp) (hD.2 P h hh)
    (hD'.2 P h hh) (Eventually.of_forall fun _ => ae_of_all _ fun _ _ => rfl)
  filter_upwards [key] with ω hω
  exact Subtype.ext (ContinuousMap.ext fun p => (hω p).symm)

/-! ## Rotation covariance -/

/-- Multiplication by `a` with `‖a‖ = 1` maps `B̄_R(0)²` into itself. -/
lemma mul_mem_sqBall {a : ℂ} (ha : ‖a‖ = 1) (R : ℝ) (p : ℂ × ℂ) (hp : p ∈ sqBall R) :
    (a * p.1, a * p.2) ∈ sqBall R := by
  obtain ⟨h1, h2⟩ := hp
  rw [mem_closedBall_zero_iff] at h1 h2
  refine ⟨?_, ?_⟩ <;> rw [mem_closedBall_zero_iff, norm_mul, ha, one_mul] <;> assumption

/-- **Rotation covariance of the canonical γ-LQG metric** (blueprint Proposition
`prop:metric-facts` (F3), rotation case), for a whole-plane GFF plus a bounded continuous
function `h`: for `‖a‖ = 1`, almost surely `D_{h(a·)}(u, v) = D_h(a u, a v)` for all `u, v`. -/
theorem IsCanonicalLQGMetric.ae_rotDist_of_isGFFPlusBddCont {γ : ℝ} {D : DistC → ContMetric}
    (hD : IsCanonicalLQGMetric γ D) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsGFFPlusBddCont h P) {a : ℂ}
    (ha : ‖a‖ = 1) :
    ∀ᵐ ω ∂P, ∀ u v : ℂ, (D (rotDist a (h ω))).1 (u, v) = (D (h ω)).1 (a * u, a * v) := by
  have hX := hD.2 P h hh
  have hX' := hD.2 P (fun ω => rotDist a (h ω)) (isGFFPlusBddCont_rotDist hh ha)
  have hXX' : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ ω ∂P, ∀ p : ℂ × ℂ,
      ((aEps (xiGamma γ) ε)⁻¹ • lfppDist (xiGamma γ) ε (rotDist a (h ω))) p =
        ((aEps (xiGamma γ) ε)⁻¹ • lfppDist (xiGamma γ) ε (h ω)) (a * p.1, a * p.2) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    filter_upwards [ae_lfppDistE_rotDist_of_isGFFPlusBddCont hh (xiGamma γ) (ne_of_gt hε) ha]
      with ω hω p
    simp only [Pi.smul_apply, smul_eq_mul, lfppDist]
    rw [hω]
  have key := ae_eq_comp_of_tendstoInProbLU (T := fun p : ℂ × ℂ => (a * p.1, a * p.2))
    (fun R p hp => mul_mem_sqBall ha R p hp) hX hX' hXX'
  filter_upwards [key] with ω hω u v
  exact hω (u, v)

/-- **Rotation covariance of the canonical γ-LQG metric** (blueprint Proposition
`prop:metric-facts` (F3), rotation case). For a canonical γ-LQG metric `D`, a whole-plane GFF `h`
(any additive constant; in particular a normalized one) and `‖a‖ = 1`, almost surely
`D_{h(a·)}(u, v) = D_h(a u, a v)` for all `u, v`. -/
theorem IsCanonicalLQGMetric.ae_rotDist {γ : ℝ} {D : DistC → ContMetric}
    (hD : IsCanonicalLQGMetric γ D) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {a : ℂ}
    (ha : ‖a‖ = 1) :
    ∀ᵐ ω ∂P, ∀ u v : ℂ, (D (rotDist a (h ω))).1 (u, v) = (D (h ω)).1 (a * u, a * v) :=
  hD.ae_rotDist_of_isGFFPlusBddCont (isGFFPlusBddCont_of_isWholePlaneGFF hh) ha

end GaussianLQG
