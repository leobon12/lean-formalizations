import SupercriticalConformalCovariance.BiLip.Target
import SupercriticalConformalCovariance.BiLip.Geom

/-!
# Lemma 2.1: target quantities on round annuli in the target coordinates

The paper's `e(around A_{r,2r}(z))` and `e(across A_{r/2,r}(z))` (l. 128–132) are compared, at small scales,
with the `e`-around and `e`-across of ROUND annuli around `φ(z)` of radii comparable to `ρ = r |φ′(z)|`
(the sandwich of l. 112–125):
* `tAround D₀ ξ k c a b`: infimum of the `e`-lengths (`dV`-lengths) of `D₀`-curves in the open round
  annulus `A_{a,b}(c)` which separate its boundary circles;
* `tAcr D₀ ξ k c a b`: infimum of the `e`-lengths of `D₀`-curves in the closed annulus `cl A_{a,b}(c)`
  from `∂B_a(c)` to `∂B_b(c)`.

With `GeomGood φ U z r ε` (`ε ≤ 1/32`):
* `isGoodLoop_of_tAround_lt`: a `tAround` loop of `A_{9ρ/8, 15ρ/8}(φ z)` pulls back by `φ⁻¹` to a source loop
  in `A_{r,2r}(z)` separating `∂B_r(z)` from `∂B_{2r}(z)` (`disconnects_pullback`), whose
  `e(·,·;B̄_{2r}(z))`-diameter is at most its `e`-length;
* `tAcr_le_lenT`: every admissible source path crossing `A_{r/2,r}(z)` has `e`-length at least
  `tAcr` of `cl A_{5ρ/8, 7ρ/8}(φ z)`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology
open scoped ENNReal

namespace SupercriticalConformalCovariance.BiLip

open SupercriticalLQGUniqueness (LSCMetric Disconnects)
open SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier (forget)
open SupercriticalConformalCovariance.Domain (dV SV)
open HigherDimLQGMetric (curveLengthWith internalWith)

section Defs

variable (D₀ : LSCMetric) (ξ : ℝ) {V : Set ℂ} (k : C(V, ℝ))

/-- `e(around A_{a,b}(c))` for a round target annulus -/
def tAround (c : ℂ) (a b : ℝ) : ℝ≥0∞ :=
  ⨅ (η : ℝ → ℂ) (s₀ : ℝ) (s₁ : ℝ) (_ : D₀.IsCurve η s₀ s₁)
    (_ : ∀ t ∈ Icc s₀ s₁, η t ∈ ball c b \ closedBall c a)
    (_ : Disconnects (η '' Icc s₀ s₁) (sphere c a) (sphere c b)),
    curveLengthWith (dV D₀ ξ k) (D₀.pt ∘ η) s₀ s₁

/-- `e(across cl A_{a,b}(c))` for a round target annulus -/
def tAcr (c : ℂ) (a b : ℝ) : ℝ≥0∞ :=
  ⨅ (η : ℝ → ℂ) (s₀ : ℝ) (s₁ : ℝ) (_ : D₀.IsCurve η s₀ s₁)
    (_ : ∀ t ∈ Icc s₀ s₁, η t ∈ closedBall c b \ ball c a)
    (_ : η s₀ ∈ sphere c a) (_ : η s₁ ∈ sphere c b),
    curveLengthWith (dV D₀ ξ k) (D₀.pt ∘ η) s₀ s₁

end Defs

/-! ## Consequences of the geometry -/

section Geometry

variable {φ : ℂ → ℂ} {U : Set ℂ} {z : ℂ} {r ε : ℝ}

theorem geom_norm_fwd (hG : GeomGood φ U z r ε) {x : ℂ} (hx : x ∈ closedBall z (3 * r)) :
    ‖φ x - φ z‖ ≤ ‖x - z‖ * ‖deriv φ z‖ + ε * (r * ‖deriv φ z‖) ∧
      ‖x - z‖ * ‖deriv φ z‖ - ε * (r * ‖deriv φ z‖) ≤ ‖φ x - φ z‖ := by
  have h := hG.2.2.2.1 x hx
  have e : ‖deriv φ z * (x - z)‖ = ‖x - z‖ * ‖deriv φ z‖ := by rw [norm_mul, mul_comm]
  constructor
  · calc ‖φ x - φ z‖ = ‖deriv φ z * (x - z) + (φ x - φ z - deriv φ z * (x - z))‖ := by ring_nf
      _ ≤ ‖deriv φ z * (x - z)‖ + ‖φ x - φ z - deriv φ z * (x - z)‖ := norm_add_le _ _
      _ ≤ _ := by rw [e]; linarith
  · have h2 : ‖deriv φ z * (x - z)‖ ≤ ‖φ x - φ z‖ + ‖φ x - φ z - deriv φ z * (x - z)‖ := by
      calc ‖deriv φ z * (x - z)‖ = ‖(φ x - φ z) - (φ x - φ z - deriv φ z * (x - z))‖ := by
            ring_nf
        _ ≤ _ := norm_sub_le _ _
    rw [e] at h2; linarith

/-- the preimage of a target point near `φ z` -/
theorem geom_inv (hG : GeomGood φ U z r ε) (hinj : InjOn φ U) {y : ℂ}
    (hy : y ∈ closedBall (φ z) (3 * (r * ‖deriv φ z‖))) :
    Function.invFunOn φ U y ∈ closedBall z (4 * r) ∧ φ (Function.invFunOn φ U y) = y ∧
      ‖Function.invFunOn φ U y - z‖ ≤ ‖y - φ z‖ / ‖deriv φ z‖ + ε * r ∧
      ‖y - φ z‖ / ‖deriv φ z‖ - ε * r ≤ ‖Function.invFunOn φ U y - z‖ ∧
      ‖deriv φ z / deriv φ (Function.invFunOn φ U y) - 1‖ ≤ ε := by
  obtain ⟨x, hx, hφx, hxb, hdx⟩ := hG.2.2.2.2 y hy
  have hxU : x ∈ U := hG.2.2.1 hx
  have hex : ∃ x' ∈ U, φ x' = y := ⟨x, hxU, hφx⟩
  have hψ : Function.invFunOn φ U y = x :=
    hinj (Function.invFunOn_mem hex) hxU ((Function.invFunOn_eq hex).trans hφx.symm)
  rw [hψ]
  have e : ‖(y - φ z) / deriv φ z‖ = ‖y - φ z‖ / ‖deriv φ z‖ := norm_div _ _
  refine ⟨hx, hφx, ?_, ?_, hdx⟩
  · calc ‖x - z‖ = ‖(y - φ z) / deriv φ z + (x - z - (y - φ z) / deriv φ z)‖ := by ring_nf
      _ ≤ ‖(y - φ z) / deriv φ z‖ + ‖x - z - (y - φ z) / deriv φ z‖ := norm_add_le _ _
      _ ≤ _ := by rw [e]; linarith
  · have h2 : ‖(y - φ z) / deriv φ z‖ ≤ ‖x - z‖ + ‖x - z - (y - φ z) / deriv φ z‖ := by
      calc ‖(y - φ z) / deriv φ z‖ = ‖(x - z) - (x - z - (y - φ z) / deriv φ z)‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    rw [e] at h2; linarith

end Geometry

/-! ## Separation transfer -/

/-- A Euclidean path from the closed inner disk to the closed exterior meets every separating set
(frozen `Disconnects`; as SLU `S36.path_hits_of_disconnects`). -/
theorem path_hits_of_disconnects' {γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b)) {c : ℂ} {ρ σ : ℝ} (hρσ : ρ ≤ σ) {K : Set ℂ}
    (hK : Disconnects K (sphere c ρ) (sphere c σ))
    (hstart : dist (γ a) c ≤ ρ) (hend : σ ≤ dist (γ b) c) :
    ∃ t ∈ Icc a b, γ t ∈ K := by
  by_contra hno
  push Not at hno
  apply hK
  have hf : ContinuousOn (fun t => dist (γ t) c) (Icc a b) :=
    continuous_dist.comp_continuousOn (hγ.prodMk continuousOn_const)
  refine ⟨γ '' Icc a b, isPreconnected_Icc.image γ hγ, ?_, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact hno t ht
  · obtain ⟨t, ht, hteq⟩ := intermediate_value_Icc hab hf ⟨hstart, hρσ.trans hend⟩
    exact ⟨γ t, ⟨t, ht, rfl⟩, mem_sphere.mpr hteq⟩
  · obtain ⟨t, ht, hteq⟩ := intermediate_value_Icc hab hf ⟨hstart.trans hρσ, hend⟩
    exact ⟨γ t, ⟨t, ht, rfl⟩, mem_sphere.mpr hteq⟩

/-- **Pull-back of a separating loop** (the sandwich topology of l. 112–125): a closed set `K` of the
target separating `∂B_{9ρ/8}(φ z)` from `∂B_{15ρ/8}(φ z)` pulls back to a set separating `∂B_r(z)` from
`∂B_{2r}(z)`. -/
theorem disconnects_pullback {φ : ℂ → ℂ} {U : Set ℂ} {z : ℂ} {r ε : ℝ}
    (hG : GeomGood φ U z r ε) (hε : ε ≤ 1 / 32) (hφc : ContinuousOn φ U) (hinj : InjOn φ U)
    {K : Set ℂ} (hKsep : Disconnects K (sphere (φ z) (9 / 8 * (r * ‖deriv φ z‖)))
      (sphere (φ z) (15 / 8 * (r * ‖deriv φ z‖))))
    (hKc : IsClosed (Function.invFunOn φ U '' K)) :
    Disconnects (Function.invFunOn φ U '' K) (sphere z r) (sphere z (2 * r)) := by
  have hr := hG.1
  have hφd : 0 < ‖deriv φ z‖ := norm_pos_iff.2 hG.2.1
  set ρ := r * ‖deriv φ z‖ with hρ
  have hρpos : 0 < ρ := mul_pos hr hφd
  rw [SupercriticalLQGUniqueness.disconnects_iff_lqgMetric_disconnects hKc]
  intro x y p hx hy
  set γ : ℝ → ℂ := fun t => p.extend t with hγ
  have hγc : Continuous γ := p.extend.continuous
  have hf : ContinuousOn (fun t => dist (γ t) z) (Icc 0 1) :=
    (continuous_dist.comp (hγc.prodMk continuous_const)).continuousOn
  have h0 : dist (γ 0) z = r := by simp only [hγ, Path.extend_zero]; exact mem_sphere.1 hx
  have h1 : dist (γ 1) z = 2 * r := by simp only [hγ, Path.extend_one]; exact mem_sphere.1 hy
  obtain ⟨s, t, hs0, hst, ht1, hs, ht, hmid⟩ :=
    LQGMetric.RectCross.exists_sub_crossing zero_le_one hf (by linarith : r ≤ 2 * r) h0.le h1.ge
  have hin : ∀ u ∈ Icc s t, γ u ∈ closedBall z (3 * r) := fun u hu => by
    rw [mem_closedBall]; linarith [(hmid u hu).2]
  have hU : ∀ u ∈ Icc s t, γ u ∈ U := fun u hu =>
    hG.2.2.1 (closedBall_subset_closedBall (by linarith) (hin u hu))
  have hgc : ContinuousOn (fun u => φ (γ u)) (Icc s t) :=
    hφc.comp hγc.continuousOn hU
  have hstart : dist (φ (γ s)) (φ z) ≤ 9 / 8 * ρ := by
    have := (geom_norm_fwd hG (hin s ⟨le_rfl, hst⟩)).1
    have hsn : ‖γ s - z‖ = r := by rw [← dist_eq_norm]; exact hs
    rw [dist_eq_norm]; rw [hsn] at this; nlinarith
  have hend : 15 / 8 * ρ ≤ dist (φ (γ t)) (φ z) := by
    have := (geom_norm_fwd hG (hin t ⟨hst, le_rfl⟩)).2
    have htn : ‖γ t - z‖ = 2 * r := by rw [← dist_eq_norm]; exact ht
    rw [dist_eq_norm]; rw [htn] at this; nlinarith
  obtain ⟨u, hu, hK⟩ := path_hits_of_disconnects' hst hgc (by nlinarith) hKsep hstart hend
  have hψ : Function.invFunOn φ U (φ (γ u)) = γ u :=
    hinj.leftInvOn_invFunOn (hU u hu)
  refine ⟨γ u, ⟨⟨u, ⟨hs0.trans hu.1, hu.2.trans ht1⟩⟩, ?_⟩, ⟨φ (γ u), hK, hψ⟩⟩
  simp only [hγ, Path.extend_apply p ⟨hs0.trans hu.1, hu.2.trans ht1⟩]

/-! ## The chain inputs from the round target events -/

/-- **Direction `e ≤ C d`: the good loop.** A `tAround` loop of `A_{9ρ/8, 15ρ/8}(φ z)` of `e`-length `< M`
gives a good loop of `e(·,·;B̄_{2r}(z))`-diameter `< M` around `B̄_r(z)`. -/
theorem isGoodLoop_of_tAround_lt {D₀ : LSCMetric} (hf₀ : Continuous (forget D₀)) {ξ : ℝ}
    {V : Set ℂ} (k : C(V, ℝ)) {φ : ℂ → ℂ} {U : Set ℂ} {z : ℂ} {r ε : ℝ}
    (hG : GeomGood φ U z r ε) (hε : ε ≤ 1 / 32) (hφc : ContinuousOn φ U) (hinj : InjOn φ U)
    (hψc : ContinuousOn (Function.invFunOn φ U) (φ '' U)) {M : ℝ≥0∞}
    (hM : tAround D₀ ξ k (φ z) (9 / 8 * (r * ‖deriv φ z‖)) (15 / 8 * (r * ‖deriv φ z‖)) < M) :
    IsGoodLoop (confT D₀ ξ k φ (closedBall z (2 * r))) (closedBall z (2 * r)) z r M := by
  have hr := hG.1
  have hφd : 0 < ‖deriv φ z‖ := norm_pos_iff.2 hG.2.1
  set ρ := r * ‖deriv φ z‖ with hρ
  have hρpos : 0 < ρ := mul_pos hr hφd
  set ψ := Function.invFunOn φ U with hψdef
  unfold tAround at hM
  simp only [iInf_lt_iff] at hM
  obtain ⟨η, s₀, s₁, hη, hηA, hdisc, hlen⟩ := hM
  have hηE : ContinuousOn η (Icc s₀ s₁) := curve_continuousOn hf₀ hη
  have hηB : ∀ t ∈ Icc s₀ s₁, η t ∈ closedBall (φ z) (3 * ρ) := fun t ht =>
    closedBall_subset_closedBall (by nlinarith) (ball_subset_closedBall (hηA t ht).1)
  have hinv := fun t ht => geom_inv hG hinj (hηB t ht)
  have hηimg : ∀ t ∈ Icc s₀ s₁, η t ∈ φ '' U := fun t ht =>
    ⟨ψ (η t), hG.2.2.1 (hinv t ht).1, (hinv t ht).2.1⟩
  set γ : ℝ → ℂ := fun t => ψ (η t) with hγ
  have hγc : ContinuousOn γ (Icc s₀ s₁) := hψc.comp hηE hηimg
  have hφγ : ∀ t ∈ Icc s₀ s₁, φ (γ t) = η t := fun t ht => (hinv t ht).2.1
  have hγA : ∀ t ∈ Icc s₀ s₁, r < ‖γ t - z‖ ∧ ‖γ t - z‖ < 2 * r := by
    intro t ht
    obtain ⟨-, -, hup, hlo, -⟩ := hinv t ht
    have hA := hηA t ht
    have h1 : 9 / 8 * ρ < ‖η t - φ z‖ := by
      have := hA.2; rw [mem_closedBall, not_le, dist_eq_norm] at this; exact this
    have h2 : ‖η t - φ z‖ < 15 / 8 * ρ := by
      have := hA.1; rw [mem_ball, dist_eq_norm] at this; exact this
    have h1' : 9 / 8 * r < ‖η t - φ z‖ / ‖deriv φ z‖ := by
      rw [lt_div_iff₀ hφd]; nlinarith
    have h2' : ‖η t - φ z‖ / ‖deriv φ z‖ < 15 / 8 * r := by
      rw [div_lt_iff₀ hφd]; nlinarith
    constructor <;> nlinarith
  have hγB : ∀ t ∈ Icc s₀ s₁, γ t ∈ closedBall z (2 * r) := fun t ht => by
    rw [mem_closedBall, dist_eq_norm]; exact (hγA t ht).2.le
  have himg : γ '' Icc s₀ s₁ = ψ '' (η '' Icc s₀ s₁) := by rw [image_image]
  have hcpt : IsCompact (γ '' Icc s₀ s₁) := isCompact_Icc.image_of_continuousOn hγc
  have hsep : Disconnects (γ '' Icc s₀ s₁) (sphere z r) (sphere z (2 * r)) := by
    rw [himg]
    refine disconnects_pullback hG hε hφc hinj hdisc ?_
    rw [← himg]; exact hcpt.isClosed
  have hdiam : ∀ s ∈ Icc s₀ s₁, ∀ t ∈ Icc s₀ s₁, s ≤ t →
      confT D₀ ξ k φ (closedBall z (2 * r)) (γ s) (γ t) ≤
        curveLengthWith (dV D₀ ξ k) (D₀.pt ∘ η) s₀ s₁ := by
    intro s hs t ht hst
    have h := internalWith_le_curveLengthWith (dV D₀ ξ k)
      (S := SV D₀ (φ '' closedBall z (2 * r))) (Q := D₀.pt ∘ η) hst
      (hη.2.mono (Icc_subset_Icc hs.1 ht.2))
      (fun u hu => ⟨γ u, hγB u ⟨hs.1.trans hu.1, hu.2.trans ht.2⟩,
        hφγ u ⟨hs.1.trans hu.1, hu.2.trans ht.2⟩⟩)
    have e : confT D₀ ξ k φ (closedBall z (2 * r)) (γ s) (γ t) =
        internalWith (dV D₀ ξ k) (SV D₀ (φ '' closedBall z (2 * r))) ((D₀.pt ∘ η) s)
          ((D₀.pt ∘ η) t) := by
      simp only [confT, Function.comp_apply, hφγ s hs, hφγ t ht]
    rw [e]
    exact h.trans (HigherDimLQGMetric.curveLengthWith_mono_interval hs.1 hst ht.2)
  refine ⟨γ '' Icc s₀ s₁, ⟨γ s₀, s₀, ⟨le_rfl, hη.1⟩, rfl⟩, isPreconnected_Icc.image _ hγc, ?_, ?_,
    ?_, SupercriticalLQGUniqueness.B2.PfeLocal.l4_closedBall_subset_fill hsep,
    curveLengthWith (dV D₀ ξ k) (D₀.pt ∘ η) s₀ s₁, hlen, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩; exact hγB t ht
  · rintro _ ⟨t, ht, rfl⟩; exact hγB t ht
  · rw [Set.disjoint_left]
    rintro _ ⟨t, ht, rfl⟩ hb
    rw [mem_ball, dist_eq_norm] at hb
    exact absurd (hγA t ht).1 (not_lt.2 hb.le)
  · rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    rcases le_total s t with hst | hts
    · exact hdiam s hs t ht hst
    · have h := internalWith_le_curveLengthWith_rev (dV D₀ ξ k)
        (fun x y => HigherDimLQGMetric.weylDistOn_comm x y)
        (S := SV D₀ (φ '' closedBall z (2 * r))) (Q := D₀.pt ∘ η) hts
        (hη.2.mono (Icc_subset_Icc ht.1 hs.2))
        (fun u hu => ⟨γ u, hγB u ⟨ht.1.trans hu.1, hu.2.trans hs.2⟩,
          hφγ u ⟨ht.1.trans hu.1, hu.2.trans hs.2⟩⟩)
      have e : confT D₀ ξ k φ (closedBall z (2 * r)) (γ s) (γ t) =
          internalWith (dV D₀ ξ k) (SV D₀ (φ '' closedBall z (2 * r))) ((D₀.pt ∘ η) s)
            ((D₀.pt ∘ η) t) := by
        simp only [confT, Function.comp_apply, hφγ s hs, hφγ t ht]
      rw [e]
      exact h.trans (HigherDimLQGMetric.curveLengthWith_mono_interval ht.1 hts hs.2)

/-- **Direction `d ≤ C e`: the crossing charge.** An admissible source path crossing `A_{r/2,r}(z)` has
`e`-length at least `tAcr` of `cl A_{5ρ/8, 7ρ/8}(φ z)`. -/
theorem tAcr_le_lenT {D₀ : LSCMetric} {ξ : ℝ} {V : Set ℂ} (k : C(V, ℝ)) {φ : ℂ → ℂ}
    {U : Set ℂ} {z : ℂ} {r ε : ℝ} (hG : GeomGood φ U z r ε) (hε : ε ≤ 1 / 32)
    (hφc : ContinuousOn φ U) {P : ℝ → ℂ} {a b : ℝ} (hP : AdmT D₀ φ U P a b) (τ t : ℝ)
    (haτ : a ≤ τ) (hτt : τ ≤ t) (htb : t ≤ b) (h1 : dist (P τ) z ≤ r / 2)
    (h2 : r ≤ dist (P t) z) :
    tAcr D₀ ξ k (φ z) (5 / 8 * (r * ‖deriv φ z‖)) (7 / 8 * (r * ‖deriv φ z‖)) ≤
      lenT D₀ ξ k φ P τ t := by
  have hr := hG.1
  have hφd : 0 < ‖deriv φ z‖ := norm_pos_iff.2 hG.2.1
  set ρ := r * ‖deriv φ z‖ with hρ
  have hρpos : 0 < ρ := mul_pos hr hφd
  have hPc : ContinuousOn P (Icc τ t) := hP.2.1.mono (Icc_subset_Icc haτ htb)
  have hf : ContinuousOn (fun u => dist (P u) z) (Icc τ t) :=
    continuous_dist.comp_continuousOn (hPc.prodMk continuousOn_const)
  obtain ⟨s, s', hτs, hss', hs't, hs, hs', hmid⟩ :=
    LQGMetric.RectCross.exists_sub_crossing hτt hf (by linarith : r / 2 ≤ r) h1 h2
  have hin : ∀ u ∈ Icc s s', P u ∈ closedBall z (3 * r) := fun u hu => by
    rw [mem_closedBall]; linarith [(hmid u hu).2]
  have hU : ∀ u ∈ Icc s s', P u ∈ U := fun u hu =>
    hG.2.2.1 (closedBall_subset_closedBall (by linarith) (hin u hu))
  have hgc : ContinuousOn (fun u => dist (φ (P u)) (φ z)) (Icc s s') :=
    continuous_dist.comp_continuousOn
      ((hφc.comp (hPc.mono (Icc_subset_Icc hτs hs't)) hU).prodMk continuousOn_const)
  have hstart : dist (φ (P s)) (φ z) ≤ 5 / 8 * ρ := by
    have := (geom_norm_fwd hG (hin s ⟨le_rfl, hss'⟩)).1
    have hsn : ‖P s - z‖ = r / 2 := by rw [← dist_eq_norm]; exact hs
    rw [dist_eq_norm]; rw [hsn] at this; nlinarith
  have hend : 7 / 8 * ρ ≤ dist (φ (P s')) (φ z) := by
    have := (geom_norm_fwd hG (hin s' ⟨hss', le_rfl⟩)).2
    have hsn : ‖P s' - z‖ = r := by rw [← dist_eq_norm]; exact hs'
    rw [dist_eq_norm]; rw [hsn] at this; nlinarith
  obtain ⟨s₂, s₃, hs₂, h23, hs₃, hg2, hg3, hmid2⟩ :=
    LQGMetric.RectCross.exists_sub_crossing hss' hgc (by nlinarith) hstart hend
  have hcurve : D₀.IsCurve (φ ∘ P) s₂ s₃ :=
    ⟨h23, hP.2.2.1.mono (Icc_subset_Icc (haτ.trans (hτs.trans hs₂))
      (hs₃.trans (hs't.trans htb)))⟩
  have hle : tAcr D₀ ξ k (φ z) (5 / 8 * ρ) (7 / 8 * ρ) ≤
      curveLengthWith (dV D₀ ξ k) (D₀.pt ∘ (φ ∘ P)) s₂ s₃ := by
    unfold tAcr
    refine iInf_le_of_le (φ ∘ P) <| iInf_le_of_le s₂ <| iInf_le_of_le s₃ <|
      iInf_le_of_le hcurve <| iInf_le_of_le ?_ <| iInf_le_of_le (mem_sphere.2 hg2) <|
      iInf_le_of_le (mem_sphere.2 hg3) le_rfl
    intro u hu
    have := hmid2 u hu
    refine ⟨mem_closedBall.2 this.2, ?_⟩
    rw [mem_ball, not_lt]; exact this.1
  exact hle.trans (HigherDimLQGMetric.curveLengthWith_mono_interval (hτs.trans hs₂) h23
    (hs₃.trans hs't))

end SupercriticalConformalCovariance.BiLip
