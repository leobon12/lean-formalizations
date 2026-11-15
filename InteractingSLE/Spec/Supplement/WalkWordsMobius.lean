/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkWordsPocket
import InteractingSLE.Foundations.PrimeEnd.Basic

/-!
# The walk order of every component chart between two ordered simple proper walls

Packet PROVE-WALK-WORDS (the input `WalkComponentWalkOrderStatement`). Every conformal bijection `g : C → ℍ` of a
component between two simple proper walls whose inverse lands on `R` at positive and on `L` at negative real points is
`m ∘ f` for PROVE-ORIENT's pocket chart `f` and a real Möbius map `m` (`HChart.exists_realMobius`). The landing
condition forces `m⁻¹(x)` to have the sign of `x` wherever a sign change would put a nondegenerate arc into
`R ∩ L`; with no common continuum of the two walls this forces `m⁻¹(x) = λ x` with `λ > 0`
(`eq_zero_of_forall_nonneg`: a real Möbius map `x ↦ (a x + b)/(c x + d)` with `x · m(x) ≥ 0` everywhere has
`c = b = 0`). So `g` inherits the walk order of the pocket chart (`WalkWordsPocket.walkOrder_of_pocketExt`):
**`walkOrder_of_isConformalBijection`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology Function Metric
open QuantumZipper (H Hbar isOpen_H)
open QuantumZipper.CA (cayley cayleyInv realMobius)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Theorem14.WalkWords

/-! ### Real Möbius maps preserving the sign of every real point -/

/-- **A real Möbius map `x ↦ (a x + b)/(c x + d)` of positive determinant with `x (a x + b)(c x + d) ≥ 0` for every
real `x` is a positive dilation**: `c = 0` and `b = 0`. -/
theorem eq_zero_of_forall_nonneg {a b c d : ℝ} (hdet : 0 < a * d - b * c)
    (hq : ∀ x : ℝ, 0 ≤ x * ((a * x + b) * (c * x + d))) : c = 0 ∧ b = 0 := by
  have hS := le_abs_self (a * d + b * c)
  have hS' := neg_abs_le (a * d + b * c)
  have hB := le_abs_self (b * d)
  have hB' := neg_abs_le (b * d)
  have hac : a * c = 0 := by
    by_contra hA
    have hApos : 0 < |a * c| := abs_pos.2 hA
    set M : ℝ := (|a * d + b * c| + |b * d|) / |a * c| + 1 with hM
    have hM0 : 0 ≤ (|a * d + b * c| + |b * d|) / |a * c| := by positivity
    have hM1 : 1 ≤ M := by linarith
    have hAM : |a * c| * M = |a * d + b * c| + |b * d| + |a * c| := by
      rw [hM, mul_add, mul_div_cancel₀ _ hApos.ne', mul_one]
    have hBM : |b * d| ≤ |b * d| * M := le_mul_of_one_le_right (abs_nonneg _) hM1
    rcases lt_or_gt_of_ne hA with hneg | hpos
    · have habs : |a * c| = -(a * c) := abs_of_neg hneg
      have h3 : a * c * M * M = -(|a * d + b * c| + |b * d| + |a * c|) * M := by
        rw [← hAM, habs]; ring
      have h2 : a * c * M * M + (a * d + b * c) * M + b * d < 0 := by
        nlinarith [mul_le_mul_of_nonneg_right hS (by linarith : (0 : ℝ) ≤ M)]
      have h1 := hq M
      have e : M * ((a * M + b) * (c * M + d)) = M * (a * c * M * M + (a * d + b * c) * M + b * d) := by ring
      rw [e] at h1
      nlinarith
    · have habs : |a * c| = a * c := abs_of_pos hpos
      have h3 : a * c * M * M = (|a * d + b * c| + |b * d| + |a * c|) * M := by
        rw [← hAM, habs]
      have h2 : 0 < a * c * M * M - (a * d + b * c) * M + b * d := by
        nlinarith [mul_le_mul_of_nonneg_right hS' (by linarith : (0 : ℝ) ≤ M)]
      have h1 := hq (-M)
      have e : -M * ((a * -M + b) * (c * -M + d)) = -M * (a * c * M * M - (a * d + b * c) * M + b * d) := by
        ring
      rw [e] at h1
      nlinarith
  rcases eq_or_ne c 0 with hc | hc
  · refine ⟨hc, ?_⟩
    subst hc
    have had : 0 < a * d := by linarith
    have ha : a ≠ 0 := by rintro rfl; simp at had
    by_contra hb
    have hb2 : 0 < b ^ 2 := lt_of_le_of_ne (sq_nonneg b) (Ne.symm (pow_ne_zero 2 hb))
    have h1 := hq (-b / (2 * a))
    have e : -b / (2 * a) * ((a * (-b / (2 * a)) + b) * (0 * (-b / (2 * a)) + d)) =
        -(b ^ 2 * (a * d) / (4 * a ^ 2)) := by
      field_simp
      ring
    rw [e] at h1
    have : 0 < b ^ 2 * (a * d) / (4 * a ^ 2) := by positivity
    linarith
  · exfalso
    have ha : a = 0 := (mul_eq_zero.1 hac).resolve_right hc
    subst ha
    have hbc : b * c < 0 := by linarith
    have hBpos : 0 < |b * c| := abs_pos.2 hbc.ne
    set M : ℝ := |b * d| / |b * c| + 1 with hM
    have hM0 : 0 ≤ |b * d| / |b * c| := by positivity
    have hAM : |b * c| * M = |b * d| + |b * c| := by
      rw [hM, mul_add, mul_div_cancel₀ _ hBpos.ne', mul_one]
    have habs : |b * c| = -(b * c) := abs_of_neg hbc
    have h2 : b * c * M + b * d < 0 := by nlinarith
    have h1 := hq M
    have e : M * ((0 * M + b) * (c * M + d)) = M * (b * c * M + b * d) := by ring
    rw [e] at h1
    nlinarith

/-! ### Every chart of the component -/

/-- **Every chart of a component between two ordered simple proper walls** with the contact order and no common
continuum is the pocket chart up to a positive dilation: its inverse lands at `x` on `G(λ x)` for the extended inverse
`G` of the pocket chart (continuous and injective on `ℍ̄`, with the walk order) and some `λ > 0`. -/
theorem exists_ext_of_isConformalBijection {R L : ℝ≥0 → ℂ} (hR : Sec7.Lemma71I.IsSimpleProper R)
    (hL : Sec7.Lemma71I.IsSimpleProper L) (hLR : range L ⊆ closedLeftSide R)
    (hco : ∀ s s' t t' : ℝ≥0, R s = L t → R s' = L t' → (s < s' ↔ t < t'))
    (hnc : ∀ S ⊆ range R ∩ range L, IsPreconnected S → S.Subsingleton) {C : Set ℂ}
    (hC : C ∈ betweenComponents (range R) (range L)) {g : ℂ → ℂ} (hg : IsConformalBijection g C H)
    (hland : ∀ x : ℝ, ∃ p : ℂ, Tendsto (invFunOn g C) (𝓝[H] (x : ℂ)) (𝓝 p) ∧
      (0 < x → p ∈ range R) ∧ (x < 0 → p ∈ range L)) :
    ∃ (G : ℂ → ℂ) (lam : ℝ), ContinuousOn G Hbar ∧ InjOn G Hbar ∧ 0 < lam ∧
      (∀ x : ℝ, Tendsto (invFunOn g C) (𝓝[H] (x : ℂ)) (𝓝 (G ((lam * x : ℝ) : ℂ)))) ∧
      (∀ (x x' : ℝ) (v v' : ℝ≥0), 0 < x → x < x' → G x = R v → G x' = R v' → v < v') ∧
      (∀ (x x' : ℝ) (v v' : ℝ≥0), x < x' → x' < 0 → G x = L v → G x' = L v' → v' < v) := by
  obtain ⟨f, G, hf, hGc, hGi, hGinv, hGL, hGR, t₀, h0, hfar⟩ := exists_pocketExt hR hL hLR hC
  obtain ⟨hoR, hoL⟩ := walkOrder_of_pocketExt hR hL hco hGc hGi hGL hGR h0 hfar
  have hRc := GW3SidedProof.isClosed_range_of_isSimpleProper hR
  have hLc := GW3SidedProof.isClosed_range_of_isSimpleProper hL
  obtain ⟨z₀, -, -, -, hCz⟩ := id hC
  have hCo : IsOpen C := hCz ▸ (isOpen_H.sdiff (hRc.union hLc)).connectedComponentIn
  obtain ⟨a, b, c, d, hdet, hEq⟩ := HChart.exists_realMobius ⟨g, hg⟩ hCo ⟨f, hf⟩
  have hxH : ∀ x : ℝ, (x : ℂ) ∈ Hbar := fun x => show (0 : ℝ) ≤ (x : ℂ).im by simp
  have hinv : ∀ ζ ∈ H, invFunOn g C ζ = G (realMobius a b c d ζ) := fun ζ hζ => by
    refine (HChart.invFunOn_eq_invFunOn_realMobius ⟨g, hg⟩ ⟨f, hf⟩ hEq hζ).trans ?_
    have hm := QuantumZipper.CA.realMobius_mem_H hdet hζ
    exact (hGinv _ hm _ (invFunOn_mem (hf.2.surjOn hm)) (invFunOn_eq (hf.2.surjOn hm))).symm
  -- the landings where the Möbius map is finite
  have hland' : ∀ x : ℝ, c * x + d ≠ 0 →
      Tendsto (invFunOn g C) (𝓝[H] (x : ℂ)) (𝓝 (G (((a * x + b) / (c * x + d) : ℝ) : ℂ))) := by
    intro x hx
    have hden : (c : ℂ) * x + d ≠ 0 := by exact_mod_cast hx
    have hval : realMobius a b c d x = (((a * x + b) / (c * x + d) : ℝ) : ℂ) := by
      simp only [QuantumZipper.CA.realMobius]; push_cast; ring
    have hm : ContinuousAt (realMobius a b c d) (x : ℂ) := by
      unfold QuantumZipper.CA.realMobius
      fun_prop (disch := exact hden)
    have hmH : Tendsto (realMobius a b c d) (𝓝[H] (x : ℂ))
        (𝓝[Hbar] (((a * x + b) / (c * x + d) : ℝ) : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun ζ hζ =>
        Sec7.Prop74B.mem_Hbar_of_mem_H (QuantumZipper.CA.realMobius_mem_H hdet hζ)⟩
      rw [← hval]
      exact hm.tendsto.mono_left nhdsWithin_le_nhds
    exact ((hGc _ (hxH _)).tendsto.comp hmH).congr'
      (eventually_nhdsWithin_of_forall fun ζ hζ => (hinv ζ hζ).symm)
  -- no sign change: otherwise an arc of `R ∩ L`
  have hq : ∀ x : ℝ, 0 ≤ x * ((a * x + b) * (c * x + d)) := by
    by_contra hneg
    simp only [not_forall, not_le] at hneg
    obtain ⟨x₀, hx₀⟩ := hneg
    have hTo : IsOpen {x : ℝ | x * ((a * x + b) * (c * x + d)) < 0} := isOpen_lt (by fun_prop) continuous_const
    have hTden : ∀ x : ℝ, x * ((a * x + b) * (c * x + d)) < 0 → c * x + d ≠ 0 := fun x hx h => by
      rw [h, mul_zero, mul_zero] at hx
      exact lt_irrefl 0 hx
    have hTRL : ∀ x : ℝ, x * ((a * x + b) * (c * x + d)) < 0 →
        G (((a * x + b) / (c * x + d) : ℝ) : ℂ) ∈ range R ∩ range L := by
      intro x hx
      have hden := hTden x hx
      obtain ⟨p, hp, hpR, hpL⟩ := hland x
      have : (𝓝[H] (x : ℂ)).NeBot := GW1P.neBot_nhdsWithin_H (hxH x)
      have hpe : p = G (((a * x + b) / (c * x + d) : ℝ) : ℂ) := tendsto_nhds_unique hp (hland' x hden)
      have hsq : 0 < (c * x + d) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hden))
      have hmul : x * ((a * x + b) / (c * x + d)) * (c * x + d) ^ 2 = x * ((a * x + b) * (c * x + d)) := by
        field_simp
      have hxμ : x * ((a * x + b) / (c * x + d)) < 0 := by
        by_contra h
        have := mul_nonneg (not_lt.1 h) hsq.le
        linarith
      rcases lt_or_gt_of_ne (show x ≠ 0 by rintro rfl; simp at hxμ) with hx0 | hx0
      · have hμ0 : 0 < (a * x + b) / (c * x + d) := by
          by_contra h
          have := mul_nonneg_of_nonpos_of_nonpos hx0.le (not_lt.1 h)
          linarith
        refine ⟨hGR _ hμ0, ?_⟩
        rw [← hpe]
        exact hpL hx0
      · have hμ0 : (a * x + b) / (c * x + d) < 0 := by
          by_contra h
          have := mul_nonneg hx0.le (not_lt.1 h)
          linarith
        refine ⟨?_, hGL _ hμ0⟩
        rw [← hpe]
        exact hpR hx0
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hTo x₀ hx₀
    have hμc : ContinuousOn (fun x : ℝ => (a * x + b) / (c * x + d)) (ball x₀ ε) := fun x hx =>
      ContinuousAt.continuousWithinAt (by fun_prop (disch := exact hTden x (hball hx)))
    have hGr : Continuous (fun y : ℝ => G y) :=
      continuousOn_univ.1 (hGc.comp continuous_ofReal.continuousOn fun y _ => hxH y)
    have hSc : IsPreconnected ((fun x : ℝ => G (((a * x + b) / (c * x + d) : ℝ) : ℂ)) '' ball x₀ ε) :=
      (convex_ball x₀ ε).isPreconnected.image _ (hGr.comp_continuousOn hμc)
    have hsub : (fun x : ℝ => G (((a * x + b) / (c * x + d) : ℝ) : ℂ)) '' ball x₀ ε ⊆ range R ∩ range L := by
      rintro _ ⟨x, hx, rfl⟩
      exact hTRL x (hball hx)
    have hx₁ : x₀ + ε / 2 ∈ ball x₀ ε := by
      rw [mem_ball, Real.dist_eq, show x₀ + ε / 2 - x₀ = ε / 2 by ring, abs_of_pos (half_pos hε)]
      exact half_lt_self hε
    have heq := hnc _ hsub hSc (mem_image_of_mem _ (mem_ball_self hε)) (mem_image_of_mem _ hx₁)
    have h1 := ofReal_injective (hGi (hxH _) (hxH _) heq)
    rw [div_eq_div_iff (hTden x₀ hx₀) (hTden _ (hball hx₁))] at h1
    have h2 : (a * d - b * c) * (x₀ - (x₀ + ε / 2)) = 0 := by linear_combination h1
    rcases mul_eq_zero.1 h2 with h | h
    · linarith
    · linarith
  obtain ⟨hc, hb⟩ := eq_zero_of_forall_nonneg hdet hq
  subst hc hb
  have had : 0 < a * d := by linarith
  have hd : d ≠ 0 := by rintro rfl; simp at had
  have hlam : 0 < a / d := by
    rcases lt_or_gt_of_ne hd with h | h
    · exact div_pos_of_neg_of_neg (by nlinarith) h
    · exact div_pos (by nlinarith) h
  have hland0 : ∀ x : ℝ, Tendsto (invFunOn g C) (𝓝[H] (x : ℂ)) (𝓝 (G ((a / d * x : ℝ) : ℂ))) := fun x => by
    have h := hland' x (by simpa using hd)
    have e : (a * x + 0) / (0 * x + d) = a / d * x := by simp only [add_zero, zero_mul, zero_add]; ring
    rwa [e] at h
  exact ⟨G, a / d, hGc, hGi, hlam, hland0, hoR, hoL⟩

/-- **The walk order of every chart of a component between two ordered simple proper walls** with the contact order
and no common continuum: the landings at `0 < x < x'` are right-wall points at parameters `v < v'`, those at
`x < x' < 0` left-wall points at parameters `v > v'`. -/
theorem walkOrder_of_isConformalBijection {R L : ℝ≥0 → ℂ} (hR : Sec7.Lemma71I.IsSimpleProper R)
    (hL : Sec7.Lemma71I.IsSimpleProper L) (hLR : range L ⊆ closedLeftSide R)
    (hco : ∀ s s' t t' : ℝ≥0, R s = L t → R s' = L t' → (s < s' ↔ t < t'))
    (hnc : ∀ S ⊆ range R ∩ range L, IsPreconnected S → S.Subsingleton) {C : Set ℂ}
    (hC : C ∈ betweenComponents (range R) (range L)) {g : ℂ → ℂ} (hg : IsConformalBijection g C H)
    (hland : ∀ x : ℝ, ∃ p : ℂ, Tendsto (invFunOn g C) (𝓝[H] (x : ℂ)) (𝓝 p) ∧
      (0 < x → p ∈ range R) ∧ (x < 0 → p ∈ range L)) :
    (∀ (x x' : ℝ) (v v' : ℝ≥0), 0 < x → x < x' → Tendsto (invFunOn g C) (𝓝[H] (x : ℂ)) (𝓝 (R v)) →
        Tendsto (invFunOn g C) (𝓝[H] (x' : ℂ)) (𝓝 (R v')) → v < v') ∧
      (∀ (x x' : ℝ) (v v' : ℝ≥0), x < x' → x' < 0 → Tendsto (invFunOn g C) (𝓝[H] (x : ℂ)) (𝓝 (L v)) →
        Tendsto (invFunOn g C) (𝓝[H] (x' : ℂ)) (𝓝 (L v')) → v' < v) := by
  obtain ⟨G, lam, -, -, hlam, hland0, hoR, hoL⟩ :=
    exists_ext_of_isConformalBijection hR hL hLR hco hnc hC hg hland
  have hxH : ∀ x : ℝ, (x : ℂ) ∈ Hbar := fun x => show (0 : ℝ) ≤ (x : ℂ).im by simp
  refine ⟨fun x x' v v' hx hxx' hv hv' => ?_, fun x x' v v' hxx' hx' hv hv' => ?_⟩
  · have : (𝓝[H] (x : ℂ)).NeBot := GW1P.neBot_nhdsWithin_H (hxH x)
    have : (𝓝[H] (x' : ℂ)).NeBot := GW1P.neBot_nhdsWithin_H (hxH x')
    exact hoR _ _ v v' (mul_pos hlam hx) (mul_lt_mul_of_pos_left hxx' hlam) (tendsto_nhds_unique (hland0 x) hv)
      (tendsto_nhds_unique (hland0 x') hv')
  · have : (𝓝[H] (x : ℂ)).NeBot := GW1P.neBot_nhdsWithin_H (hxH x)
    have : (𝓝[H] (x' : ℂ)).NeBot := GW1P.neBot_nhdsWithin_H (hxH x')
    exact hoL _ _ v v' (mul_lt_mul_of_pos_left hxx' hlam) (mul_neg_of_pos_of_neg hlam hx')
      (tendsto_nhds_unique (hland0 x) hv) (tendsto_nhds_unique (hland0 x') hv')

end InteractingSLE.Theorem14.WalkWords
