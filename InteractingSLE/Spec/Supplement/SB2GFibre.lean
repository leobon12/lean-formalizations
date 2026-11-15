/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkWordsFiber

/-!
# Two real preimages on one side of any trace point coincide

Packet PROVE-T14-SB2FIN2 (Theorem 1.4's SB2, the `cusp` field of `IsRelConfigJC`). The landed fibre lemma
`WalkWords.false_of_extendFrom_eq_of_lt` treats a trace point `η(s) ∈ ℍ`. The cusp field needs the same statement at
**real** trace points (bounce points of the relative trace on `ℝ`, and its seed `η(0) = 0`):

* **`false_of_extendFrom_eq_of_lt_gen`**: for a Loewner trace `η` of a continuous driver, injective on `[0, τ]`, and
  `s < τ`, two real preimages `y₁ < y₂` of `η(s)` under the extended inverse map of time `τ` with `0 ∉ [y₁, y₂]` are
  impossible — with no condition on `η(s)`;
* `eq_of_extendFrom_eq_of_same_side_gen`, `subsingleton_fibre_pos`, `subsingleton_fibre_neg`.

## Proof

The landed Jordan-curve argument (the upper semicircle over `[y₁, y₂]` is mapped onto a Jordan curve `J`
through `q = η(s)`; the image of the half-disc lies inside `J`; a point `F̄(m)`, `m ∈ (y₁, y₂)`, `F̄(m) ≠ q`, is
inside `J`, hence a trace point `η(u)`, `u ≠ s`, and the trace arc from `η(u)` to the tip or to the seed crosses
`J`). It used `q ∈ ℍ` only to put the closed lower half-plane outside `J`. For real `q`: `J ⊆ ℍ ∪ {q}`, so the
**open** lower half-plane is outside `J` (connected, unbounded, off `J`), and every real point `z ≠ q` is off `J`
and adherent to it, hence outside (`closure (jordanOut J) = jordanOut J ∪ J`). These two facts replace the three
uses of `q ∈ ℍ` (the inside of `J` lies in `ℍ`; the seed `η(0)` is outside `J` when `s ≠ 0`, by injectivity). `F̄`
maps `ℍ̄` into `ℍ̄` (continuity), so `Im q ≥ 0`. Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology Complex Metric Bornology
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.Theorem14.SB.FinRel

open WangWu (jordanIn jordanOut)
open InteractingSLE.Theorem14.WalkWords

section FiberGen

variable {W : ℝ → ℝ} {η : ℝ → ℂ}

/-- **Two real preimages on one side of a trace point** (contradiction form, any trace point): two preimages
`y₁ < y₂` of `η(s)`, `s < τ`, with `0 ∉ [y₁, y₂]`, are impossible. -/
theorem false_of_extendFrom_eq_of_lt_gen (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) {s τ : ℝ}
    (hs : 0 ≤ s) (hsτ : s < τ) (hinj : InjOn η (Icc 0 τ)) {y₁ y₂ : ℝ} (hy : y₁ < y₂)
    (h0 : (0 : ℝ) ∉ Icc y₁ y₂) (h₁ : extendFrom H (fwdMapInv W τ) y₁ = η s)
    (h₂ : extendFrom H (fwdMapInv W τ) y₂ = η s) : False := by
  have hτ0 : 0 ≤ τ := hs.trans hsτ.le
  set F : ℂ → ℂ := extendFrom H (fwdMapInv W τ) with hF
  obtain ⟨hFd, hFc, hFi, hFR⟩ := hη.fiber_hyps hW hW0 hτ0
  have hFH : ∀ w ∈ H, F w ∈ H := fun w hw => by
    rw [hF, ZhanGT4.extendFrom_eq_fwdMapInv hW hW0 hτ0 hw]
    exact QuantumZipper.RS.fwdMapInv_mem_H hW hW0 hτ0 hw
  have hqF : η s ∉ F '' H := trace_notMem_image_H hη hW hW0 hτ0 ⟨hs, hsτ.le⟩
  set c : ℝ := (y₁ + y₂) / 2 with hc
  set ρ : ℝ := (y₂ - y₁) / 2 with hρ
  have hρ0 : 0 < ρ := by rw [hρ]; linarith
  set A : ℝ → ℂ := semiPt c ρ with hA
  have hA0 : A 0 = (y₂ : ℂ) := by rw [hA, semiPt_zero]; congr 1; rw [hc, hρ]; ring
  have hAπ : A Real.pi = (y₁ : ℂ) := by rw [hA, semiPt_pi]; congr 1; rw [hc, hρ]; ring
  have hpi := Real.pi_pos
  -- values on the semicircle
  have hAre : ∀ θ ∈ Icc 0 Real.pi, θ = 0 ∨ θ = Real.pi → F (A θ) = η s := by
    rintro θ - (rfl | rfl)
    · rw [hA0]; exact h₂
    · rw [hAπ]; exact h₁
  have hAH : ∀ θ ∈ Icc 0 Real.pi, θ ≠ 0 → θ ≠ Real.pi → A θ ∈ H := fun θ hθ h1 h2 =>
    semiPt_mem_H hρ0 ⟨lt_of_le_of_ne hθ.1 (Ne.symm h1), lt_of_le_of_ne hθ.2 h2⟩
  have hAF : ∀ θ ∈ Icc 0 Real.pi, ∀ θ' ∈ Icc 0 Real.pi, F (A θ) = F (A θ') →
      θ = θ' ∨ ((θ = 0 ∨ θ = Real.pi) ∧ (θ' = 0 ∨ θ' = Real.pi)) := by
    intro θ hθ θ' hθ' he
    by_cases hb : θ = 0 ∨ θ = Real.pi
    · by_cases hb' : θ' = 0 ∨ θ' = Real.pi
      · exact Or.inr ⟨hb, hb'⟩
      · rw [not_or] at hb'
        exact absurd ⟨A θ', hAH θ' hθ' hb'.1 hb'.2, he.symm.trans (hAre θ hθ hb)⟩ hqF
    · rw [not_or] at hb
      by_cases hb' : θ' = 0 ∨ θ' = Real.pi
      · exact absurd ⟨A θ, hAH θ hθ hb.1 hb.2, he.trans (hAre θ' hθ' hb')⟩ hqF
      · rw [not_or] at hb'
        exact Or.inl (semiPt_injOn hρ0 hθ hθ' (hFi (hAH θ hθ hb.1 hb.2) (hAH θ' hθ' hb'.1 hb'.2) he))
  have hAc : ContinuousOn (fun θ => F (A θ)) (Icc 0 Real.pi) :=
    hFc.comp (continuous_semiPt c ρ).continuousOn fun θ hθ => semiPt_mem_Hbar hρ0.le hθ
  -- the two arcs
  set u : ℝ → ℂ := fun t => F (A (Real.pi / 2 * t)) with hu
  set v : ℝ → ℂ := fun t => F (A (Real.pi - Real.pi / 2 * t)) with hv
  have hut : ∀ t ∈ Icc (0 : ℝ) 1, Real.pi / 2 * t ∈ Icc 0 Real.pi := fun t ht =>
    ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
  have hvt : ∀ t ∈ Icc (0 : ℝ) 1, Real.pi - Real.pi / 2 * t ∈ Icc 0 Real.pi := fun t ht =>
    ⟨by nlinarith [ht.2], by nlinarith [ht.1]⟩
  have huc : ContinuousOn u (Icc 0 1) :=
    hAc.comp (by fun_prop) fun t ht => hut t ht
  have hvc : ContinuousOn v (Icc 0 1) :=
    hAc.comp (by fun_prop) fun t ht => hvt t ht
  have hui : InjOn u (Icc 0 1) := by
    intro t ht t' ht' he
    rcases hAF _ (hut t ht) _ (hut t' ht') he with h | ⟨h1, h2⟩
    · exact mul_left_cancel₀ (by positivity) h
    · have e1 : Real.pi / 2 * t = 0 := h1.resolve_right fun h => by nlinarith [ht.2]
      have e2 : Real.pi / 2 * t' = 0 := h2.resolve_right fun h => by nlinarith [ht'.2]
      exact mul_left_cancel₀ (show Real.pi / 2 ≠ 0 by positivity) (e1.trans e2.symm)
  have hvi : InjOn v (Icc 0 1) := by
    intro t ht t' ht' he
    rcases hAF _ (hvt t ht) _ (hvt t' ht') he with h | ⟨h1, h2⟩
    · have : Real.pi / 2 * t = Real.pi / 2 * t' := by linarith
      exact mul_left_cancel₀ (by positivity) this
    · have e1 : Real.pi - Real.pi / 2 * t = Real.pi := h1.resolve_left fun h => by nlinarith [ht.2]
      have e2 : Real.pi - Real.pi / 2 * t' = Real.pi := h2.resolve_left fun h => by nlinarith [ht'.2]
      have : Real.pi / 2 * t = Real.pi / 2 * t' := by linarith
      exact mul_left_cancel₀ (show Real.pi / 2 ≠ 0 by positivity) this
  have hu0 : u 0 = η s := by simp only [hu, mul_zero]; exact hAre 0 ⟨le_rfl, hpi.le⟩ (Or.inl rfl)
  have hv0 : v 0 = η s := by
    simp only [hv, mul_zero, sub_zero]; exact hAre _ ⟨hpi.le, le_rfl⟩ (Or.inr rfl)
  have huv1 : u 1 = v 1 := by simp only [hu, hv, mul_one]; congr 2; ring
  have hint : u '' Icc 0 1 ∩ v '' Icc 0 1 ⊆ {u 0, u 1} := by
    rintro z ⟨⟨t, ht, rfl⟩, ⟨t', ht', he⟩⟩
    rcases hAF _ (hut t ht) _ (hvt t' ht') he.symm with h | ⟨h1, -⟩
    · have : t = 1 := by nlinarith [ht.2, ht'.2]
      rw [this]; exact Or.inr rfl
    · have : t = 0 := by
        rcases h1 with h1 | h1
        · nlinarith
        · nlinarith [ht.2]
      rw [this]; exact Or.inl rfl
  set J : Set ℂ := u '' Icc 0 1 ∪ v '' Icc 0 1 with hJdef
  have hJ : LQGMetric.JordanMap.IsJordanCurve J :=
    Sec7.isJordanCurve_image_union huc hvc hui hvi (hu0.trans hv0.symm) huv1 hint
  -- points of `J`
  have hJpt : ∀ z ∈ J, z = η s ∨ ∃ θ ∈ Ioo 0 Real.pi, z = F (A θ) := by
    have key : ∀ θ ∈ Icc 0 Real.pi, F (A θ) = η s ∨ ∃ θ' ∈ Ioo 0 Real.pi, F (A θ) = F (A θ') := by
      intro θ hθ
      by_cases hb : θ = 0 ∨ θ = Real.pi
      · exact Or.inl (hAre θ hθ hb)
      · rw [not_or] at hb
        exact Or.inr ⟨θ, ⟨lt_of_le_of_ne hθ.1 (Ne.symm hb.1), lt_of_le_of_ne hθ.2 hb.2⟩, rfl⟩
    rintro z (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact key _ (hut t ht)
    · exact key _ (hvt t ht)
  have hJim : ∀ z ∈ J, z ≠ η s → 0 < z.im := by
    intro z hz hne
    rcases hJpt z hz with h | ⟨θ, hθ, rfl⟩
    · exact absurd h hne
    · exact hFH _ (semiPt_mem_H hρ0 hθ)
  have hFHbar : ∀ x : ℝ, 0 ≤ (F x).im := by
    intro x
    have hxb : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ ((x : ℂ)).im by simp
    have hcl : F x ∈ closure (F '' H) :=
      ContinuousWithinAt.mem_closure_image ((hFc _ hxb).mono QuantumZipper.H_subset_Hbar)
        (by rw [closure_H]; exact hxb)
    have hsub : closure (F '' H) ⊆ {z : ℂ | 0 ≤ z.im} :=
      closure_minimal (by rintro _ ⟨w, hw, rfl⟩; exact le_of_lt (show 0 < (F w).im from hFH w hw))
        (isClosed_le continuous_const continuous_im)
    exact hsub hcl
  have hηsim : 0 ≤ (η s).im := h₁ ▸ hFHbar y₁
  -- the circle points of `ℍ` map into `J`
  have hcircJ : ∀ θ ∈ Ioo 0 Real.pi, F (A θ) ∈ J := by
    intro θ hθ
    by_cases hθ2 : θ ≤ Real.pi / 2
    · refine Or.inl ⟨θ / (Real.pi / 2), ⟨div_nonneg hθ.1.le (by positivity), ?_⟩, ?_⟩
      · rw [div_le_one (by positivity)]; exact hθ2
      · simp only [hu]; congr 2; field_simp
    · refine Or.inr ⟨(Real.pi - θ) / (Real.pi / 2), ⟨div_nonneg (by linarith [hθ.2]) (by positivity), ?_⟩, ?_⟩
      · rw [div_le_one (by positivity)]; linarith
      · simp only [hv]; congr 2; field_simp; ring
  -- the lower half-plane is outside `J`
  have hunb : ¬ IsBounded {z : ℂ | z.im < 0} := by
    intro hb
    obtain ⟨M, hM⟩ := hb.subset_closedBall 0
    have hmem : -((|M| + 1 : ℝ) : ℂ) * I ∈ {z : ℂ | z.im < 0} := by
      show (-((|M| + 1 : ℝ) : ℂ) * I).im < 0
      simp only [neg_mul, neg_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
      linarith [abs_nonneg M]
    have h1 := hM hmem
    rw [mem_closedBall, dist_zero_right] at h1
    have : ‖-((|M| + 1 : ℝ) : ℂ) * I‖ = |M| + 1 := by
      rw [norm_mul, norm_neg, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith [le_abs_self M]
  have hlow : {z : ℂ | z.im < 0} ⊆ jordanOut J :=
    WangWu.subset_jordanOut_of_isPreconnected (convex_halfSpace_im_lt 0).isPreconnected hunb
      (Set.disjoint_left.2 fun z hz hzJ => by
        have hz' : z.im < 0 := hz
        by_cases he : z = η s
        · rw [he] at hz'; exact absurd hz' (not_lt.2 hηsim)
        · exact absurd hz' (not_lt.2 (hJim z hzJ he).le))
  have hrealOut : ∀ z : ℂ, z.im = 0 → z ≠ η s → z ∈ jordanOut J := by
    intro z hz hne
    have hzJ : z ∉ J := fun hzJ => absurd hz (hJim z hzJ hne).ne'
    have hcl : z ∈ closure (jordanOut J) := by
      have hcont : Continuous (fun ε : ℝ => z - (ε : ℂ) * I) := by fun_prop
      have h := hcont.tendsto 0
      simp only [ofReal_zero, zero_mul, sub_zero] at h
      refine mem_closure_of_tendsto (h.mono_left (nhdsWithin_le_nhds (s := Ioi 0))) ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      refine hlow (show (z - (ε : ℂ) * I).im < 0 from ?_)
      simp only [sub_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero, hz]
      linarith [show (0 : ℝ) < ε from hε]
    rw [Foundations.ThetaCurve.closure_jordanOut hJ] at hcl
    exact hcl.resolve_right hzJ
  -- the values off the closed disc are outside `J`
  obtain ⟨C, hC⟩ := exists_norm_fwdMapInv_sub_le hW hW0 hτ0
  have hFC : ∀ w ∈ H, ‖F w - w‖ ≤ C := fun w hw => by
    rw [hF, ZhanGT4.extendFrom_eq_fwdMapInv hW hW0 hτ0 hw]; exact hC w hw
  have hnotJ : ∀ w ∈ H, ‖w - c‖ ≠ ρ → F w ∉ J := by
    intro w hw hwc hJw
    rcases hJpt _ hJw with he | ⟨θ, hθ, he⟩
    · exact hqF ⟨w, hw, he⟩
    · have := hFi hw (semiPt_mem_H hρ0 hθ) he
      exact hwc (by rw [this]; exact norm_semiPt_sub hρ0.le θ)
  have hout : ∀ z ∈ H, ρ < ‖z - c‖ → F z ∈ jordanOut J := by
    intro z hz hzc
    set R : Set ℂ := (fun t : ℝ => z + (t : ℂ) * I) '' Ici 0 with hR
    have hRH : ∀ w ∈ R, w ∈ H ∧ ρ < ‖w - c‖ := by
      rintro _ ⟨t, ht, rfl⟩
      have hzim : 0 < z.im := hz
      have ht0 : (0 : ℝ) ≤ t := ht
      refine ⟨show 0 < (z + (t : ℂ) * I).im by simp; linarith, ?_⟩
      have h1 : ‖z - c‖ ^ 2 ≤ ‖z + (t : ℂ) * I - c‖ ^ 2 := by
        rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
        simp only [sub_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
          add_zero, sub_im, add_im, mul_im]
        nlinarith
      have h2 : 0 ≤ ‖z + (t : ℂ) * I - c‖ := norm_nonneg _
      nlinarith [norm_nonneg (z - c)]
    have hRc : IsPreconnected (F '' R) :=
      (isPreconnected_Ici.image _ (by fun_prop)).image F
        (hFc.mono fun w hw => QuantumZipper.H_subset_Hbar (hRH w hw).1)
    have hRb : ¬ IsBounded (F '' R) := by
      intro hb
      obtain ⟨M, hM⟩ := hb.subset_closedBall 0
      set t : ℝ := |M| + |C| + ‖z‖ + 1 with ht
      have ht0 : (0 : ℝ) ≤ t := by rw [ht]; positivity
      have hmem : F (z + (t : ℂ) * I) ∈ F '' R := ⟨_, ⟨t, ht0, rfl⟩, rfl⟩
      have h1 := hM hmem
      rw [mem_closedBall, dist_zero_right] at h1
      have h2 := hFC _ (hRH _ ⟨t, ht0, rfl⟩).1
      have h3 : t ≤ ‖z + (t : ℂ) * I‖ + ‖z‖ := by
        have : ‖(t : ℂ) * I‖ = t := by
          rw [norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
        calc t = ‖(t : ℂ) * I‖ := this.symm
          _ = ‖(z + (t : ℂ) * I) - z‖ := by ring_nf
          _ ≤ ‖z + (t : ℂ) * I‖ + ‖z‖ := norm_sub_le _ _
      have h4 : ‖z + (t : ℂ) * I‖ ≤ ‖F (z + (t : ℂ) * I)‖ + C := by
        have := norm_sub_le_norm_sub_add_norm_sub (z + (t : ℂ) * I) (F (z + (t : ℂ) * I)) 0
        have h5 : ‖z + (t : ℂ) * I - F (z + (t : ℂ) * I)‖ ≤ C := by rw [norm_sub_rev]; exact h2
        simp only [sub_zero] at this
        linarith
      linarith [le_abs_self M, le_abs_self C]
    have hRJ : Disjoint (F '' R) J := Set.disjoint_left.2 fun _ ⟨w, hw, he⟩ hJ' =>
      hnotJ w (hRH w hw).1 (hRH w hw).2.ne' (he ▸ hJ')
    exact WangWu.subset_jordanOut_of_isPreconnected hRc hRb hRJ ⟨z, ⟨0, Set.self_mem_Ici, by simp⟩, rfl⟩
  -- the image of the half-disc lies inside `J`
  have hFHopen : IsOpen (F '' H) := by
    have : F '' H = H \ fwdHull W τ := by
      rw [← QuantumZipper.RS.image_fwdMapInv_H hW hW0 hτ0]
      exact image_congr fun w hw => ZhanGT4.extendFrom_eq_fwdMapInv hW hW0 hτ0 hw
    rw [this]; exact (isHPHull_fwdHull hW hτ0).isOpen
  have hpi2 : Real.pi / 2 ∈ Ioo 0 Real.pi := ⟨by positivity, by linarith⟩
  have htop : F (A (Real.pi / 2)) ∈ J := hcircJ _ hpi2
  have htopH : F (A (Real.pi / 2)) ∈ F '' H := ⟨_, semiPt_mem_H hρ0 hpi2, rfl⟩
  obtain ⟨w, hwI, z, hz, rfl⟩ : (jordanIn J ∩ F '' H).Nonempty := by
    have := WangWu.mem_closure_jordanIn hJ htop
    rw [_root_.mem_closure_iff] at this
    obtain ⟨w, hw1, hw2⟩ := this _ hFHopen htopH
    exact ⟨w, hw2, hw1⟩
  have hzc : ‖z - c‖ < ρ := by
    rcases lt_trichotomy ‖z - c‖ ρ with h | h | h
    · exact h
    · obtain ⟨θ, hθ, rfl⟩ := exists_semiPt_eq hρ0 hz h
      exact absurd (hcircJ θ hθ) hwI.1
    · exact absurd (hout z hz h) (Set.disjoint_left.1 (WangWu.disjoint_jordanIn_jordanOut J) hwI)
  set Q : Set ℂ := H ∩ ball (c : ℂ) ρ with hQ
  have hQin : F '' Q ⊆ jordanIn J := by
    have hQc : IsPreconnected (F '' Q) :=
      ((convex_H.inter (convex_ball _ _)).isPreconnected).image F
        (hFc.mono fun w hw => QuantumZipper.H_subset_Hbar hw.1)
    refine WangWu.IsPreconnected.subset_jordanIn hJ hQc
      (Set.disjoint_left.2 fun _ ⟨x, hx, he⟩ hJx => ?_) ⟨_, ⟨z, ⟨hz, ?_⟩, rfl⟩, hwI⟩
    · have hx2 := hx.2
      rw [mem_ball, dist_eq_norm] at hx2
      exact hnotJ x hx.1 hx2.ne (he ▸ hJx)
    · rw [mem_ball, dist_eq_norm]; exact hzc
  -- a coordinate between `y₁` and `y₂` with another value
  obtain ⟨m, hm, hFm⟩ := exists_ne_of_injOn hFd hFc hFi hy (η s)
  have hmc : ‖(m : ℂ) - c‖ < ρ := by
    rw [← ofReal_sub, norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith [hm.1, hm.2]
  -- vertical approach to a real point
  have happroach : ∀ x : ℝ, Tendsto (fun ε : ℝ => (x : ℂ) + (ε : ℂ) * I) (𝓝[>] 0) (𝓝[H] (x : ℂ)) := by
    intro x
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hcont : Continuous (fun ε : ℝ => (x : ℂ) + (ε : ℂ) * I) := by fun_prop
      have h := hcont.tendsto 0
      simp only [ofReal_zero, zero_mul, add_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      show 0 < ((x : ℂ) + (ε : ℂ) * I).im
      simpa using hε
  have hFlim : ∀ x : ℝ, Tendsto (fun ε : ℝ => F ((x : ℂ) + (ε : ℂ) * I)) (𝓝[>] 0) (𝓝 (F x)) := by
    intro x
    have h1 : Tendsto F (𝓝[H] (x : ℂ)) (𝓝 (F x)) :=
      (hFc _ (show (0 : ℝ) ≤ ((x : ℂ)).im by simp)).tendsto.mono_left
        (nhdsWithin_mono _ QuantumZipper.H_subset_Hbar)
    exact h1.comp (happroach x)
  have hFmIn : F m ∈ jordanIn J := by
    have hcl : F m ∈ closure (jordanIn J) := by
      refine mem_closure_of_tendsto (hFlim m) ?_
      have hδ : 0 < ρ - ‖(m : ℂ) - c‖ := by linarith
      filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
      refine hQin ⟨_, ⟨?_, ?_⟩, rfl⟩
      · show 0 < ((m : ℂ) + (ε : ℂ) * I).im
        simpa using hε.1
      · rw [mem_ball, dist_eq_norm]
        calc ‖(m : ℂ) + (ε : ℂ) * I - c‖ ≤ ‖(m : ℂ) - c‖ + ‖(ε : ℂ) * I‖ := by
              rw [show (m : ℂ) + (ε : ℂ) * I - c = ((m : ℂ) - c) + (ε : ℂ) * I by ring]
              exact norm_add_le _ _
          _ < ρ := by
              rw [norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_of_pos hε.1]
              linarith [hε.2]
    rw [WangWu.closure_jordanIn hJ] at hcl
    rcases hcl with h | h
    · exact h
    · rcases hJpt _ h with he | ⟨θ, hθ, he⟩
      · exact absurd he hFm
      · exact absurd ⟨_, semiPt_mem_H hρ0 hθ, he.symm⟩ (hFR (m : ℂ) (by simp))
  have hFmH : F m ∈ H := by
    by_contra hn
    have him : (F m).im = 0 := le_antisymm (not_lt.1 hn) (hFHbar m)
    exact Set.disjoint_left.1 (WangWu.disjoint_jordanIn_jordanOut J) hFmIn (hrealOut _ him hFm)
  obtain ⟨u', hu', hu'e⟩ : F m ∈ η '' Icc 0 τ := by
    rcases WalkNorm.extendFrom_real_cases hη hW hW0 hτ0 m with h | h
    · exact absurd hFmH (by show ¬ 0 < (F m).im; rw [h]; exact lt_irrefl 0)
    · exact h
  have hu's : u' ≠ s := fun h => hFm (by rw [h] at hu'e; exact hu'e.symm)
  -- trace points other than `η s` are off `J`
  have hηJ : ∀ r ∈ Icc 0 τ, r ≠ s → η r ∉ J := by
    intro r hr hrs hJr
    rcases hJpt _ hJr with he | ⟨θ, hθ, he⟩
    · exact hrs (hinj hr ⟨hs, hsτ.le⟩ he)
    · exact trace_notMem_image_H hη hW hW0 hτ0 hr ⟨_, semiPt_mem_H hρ0 hθ, he.symm⟩
  -- the tip is outside `J`
  have hcρ : ρ < |c| := by
    simp only [mem_Icc, not_and_or, not_le] at h0
    rcases h0 with h | h
    · rw [abs_of_pos (by rw [hc]; linarith), hc, hρ]; linarith
    · rw [abs_of_neg (by rw [hc]; linarith), hc, hρ]; linarith
  have hτout : η τ ∈ jordanOut J := by
    have hη0 : F 0 = η τ := hη.loewnerTip_eq hW hW0 hτ0
    have hlim := hFlim 0
    simp only [ofReal_zero, zero_add] at hlim
    have hcl : F 0 ∈ closure (jordanOut J) := by
      refine mem_closure_of_tendsto hlim ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      refine hout _ (show 0 < ((ε : ℂ) * I).im by simpa using hε) ?_
      calc ρ < |c| := hcρ
        _ = |((ε : ℂ) * I - c).re| := by simp [abs_neg]
        _ ≤ ‖(ε : ℂ) * I - c‖ := Complex.abs_re_le_norm _
    rw [Foundations.ThetaCurve.closure_jordanOut hJ, hη0] at hcl
    rcases hcl with h | h
    · exact h
    · exact absurd h (hηJ τ ⟨hτ0, le_rfl⟩ hsτ.ne')
  have hη0out : s ≠ 0 → η 0 ∈ jordanOut J := fun hs0 =>
    hrealOut _ (by rw [hη.1]; simp) fun h => hs0 (hinj ⟨le_rfl, hτ0⟩ ⟨hs, hsτ.le⟩ h).symm
  have hηc : ContinuousOn η (Icc 0 τ) := hη.2.1.mono fun r hr => hr.1
  have hu'in : η u' ∈ jordanIn J := hu'e ▸ hFmIn
  have hdisj := WangWu.disjoint_jordanIn_jordanOut J
  rcases lt_or_gt_of_ne hu's with hlt | hgt
  · have hP : IsPreconnected (η '' Icc 0 u') :=
      isPreconnected_Icc.image η (hηc.mono (Icc_subset_Icc_right hu'.2))
    have hPJ : η '' Icc 0 u' ⊆ Jᶜ := by
      rintro _ ⟨r, hr, rfl⟩
      exact hηJ r ⟨hr.1, hr.2.trans hu'.2⟩ (ne_of_lt (lt_of_le_of_lt hr.2 hlt))
    rcases Foundations.ThetaCurve.subset_jordanIn_or_subset_jordanOut hJ hP hPJ with h | h
    · exact Set.disjoint_left.1 hdisj (h ⟨0, ⟨le_rfl, hu'.1⟩, rfl⟩)
        (hη0out fun h0 => absurd hu'.1 (not_le.2 (h0 ▸ hlt)))
    · exact Set.disjoint_left.1 hdisj hu'in (h ⟨u', ⟨hu'.1, le_rfl⟩, rfl⟩)
  · have hP : IsPreconnected (η '' Icc u' τ) :=
      isPreconnected_Icc.image η (hηc.mono (Icc_subset_Icc_left hu'.1))
    have hPJ : η '' Icc u' τ ⊆ Jᶜ := by
      rintro _ ⟨r, hr, rfl⟩
      exact hηJ r ⟨hu'.1.trans hr.1, hr.2⟩ (ne_of_gt (lt_of_lt_of_le hgt hr.1))
    rcases Foundations.ThetaCurve.subset_jordanIn_or_subset_jordanOut hJ hP hPJ with h | h
    · exact Set.disjoint_left.1 hdisj (h ⟨τ, ⟨hu'.2, le_rfl⟩, rfl⟩) hτout
    · exact Set.disjoint_left.1 hdisj hu'in (h ⟨u', ⟨le_rfl, hu'.2⟩, rfl⟩)


/-- **The fibre lemma at any trace point**: two real preimages of `η(s)`, `s < τ`, on the same side of the tip
coordinate `0` coincide. -/
theorem eq_of_extendFrom_eq_of_same_side_gen (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {s τ : ℝ} (hs : 0 ≤ s) (hsτ : s < τ) (hinj : InjOn η (Icc 0 τ)) {y₁ y₂ : ℝ}
    (hside : 0 < y₁ * y₂) (h₁ : extendFrom H (fwdMapInv W τ) y₁ = η s)
    (h₂ : extendFrom H (fwdMapInv W τ) y₂ = η s) : y₁ = y₂ := by
  rcases lt_trichotomy y₁ y₂ with h | h | h
  · refine (false_of_extendFrom_eq_of_lt_gen hη hW hW0 hs hsτ hinj h (fun h0 => ?_) h₁ h₂).elim
    nlinarith [h0.1, h0.2]
  · exact h
  · refine (false_of_extendFrom_eq_of_lt_gen hη hW hW0 hs hsτ hinj h (fun h0 => ?_) h₂ h₁).elim
    nlinarith [h0.1, h0.2]

/-- Right of the tip coordinate, a trace point `η(s)`, `s < τ`, has at most one real preimage. -/
theorem subsingleton_fibre_pos (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {s τ : ℝ} (hs : 0 ≤ s) (hsτ : s < τ) (hinj : InjOn η (Icc 0 τ)) :
    {x : ℝ | 0 < x ∧ extendFrom H (fwdMapInv W τ) x = η s}.Subsingleton := fun _ h₁ _ h₂ =>
  eq_of_extendFrom_eq_of_same_side_gen hη hW hW0 hs hsτ hinj (mul_pos h₁.1 h₂.1) h₁.2 h₂.2

/-- Left of the tip coordinate, a trace point `η(s)`, `s < τ`, has at most one real preimage. -/
theorem subsingleton_fibre_neg (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {s τ : ℝ} (hs : 0 ≤ s) (hsτ : s < τ) (hinj : InjOn η (Icc 0 τ)) :
    {x : ℝ | x < 0 ∧ extendFrom H (fwdMapInv W τ) x = η s}.Subsingleton := fun _ h₁ _ h₂ =>
  eq_of_extendFrom_eq_of_same_side_gen hη hW hW0 hs hsτ hinj (mul_pos_of_neg_of_neg h₁.1 h₂.1) h₁.2 h₂.2

end FiberGen

end InteractingSLE.Theorem14.SB.FinRel
