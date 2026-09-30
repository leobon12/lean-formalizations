import QuantumZipper.Proofs.Zipper.FieldLawler3ExistLoew

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL4-E (basic): the boundary frame of the Loewner configuration

Task FL4-E (Track A round 4). For the Loewner configuration `K = γ([0,t])`, an open arc
`η = C_ε(α, β)` and the frame
`E = K ∪ closure η ∪ (C_R ∩ {Im ≥ 0}) ∪ [-R, R]`
(`fl4eE`) we prove here:
* `fl4eE_isClosed`, `fl4eE_sub_closedBall`: `E` is closed and lies in `B̄(0, R)`;
* `fl4eE_ulc`: `E` is uniformly locally connected (a finite union of images of compact
  intervals, `Topo.ULC.image_Icc` and `Topo.ULC.union_of_isCompact_of_isClosed`);
* `fl4e_arc_diff`: attaching an injective arc minus a point to a connected set (tool for
  `E \ {q}` connected, FieldLawler4E.lean);
* `fl4e_J_diff`: the closed upper half-disc boundary `C_R⁺ ∪ [-R, R]` minus a point is connected.

These are the boundary-set hypotheses of `fl3Wd_FL3Unif_of_car` (Carathéodory's theorem,
Pommerenke 1992, Thm 2.6, p. 24). The topology is our own elementary bookkeeping (no published
source states these point-set facts for this configuration; searched `literature/` for
"uniformly locally connected" and "cut point").
-/

noncomputable section

open Set Filter Metric Complex
open scoped Topology Real

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar
open QuantumZipper.CA

/-- The boundary frame `E = K ∪ closure η ∪ (C_R ∩ {Im ≥ 0}) ∪ [-R, R]`. -/
def fl4eE (γ : ℝ → ℂ) (t R ε α β : ℝ) : Set ℂ :=
  γ '' Icc 0 t ∪ closure (flCircArc ε α β) ∪ (sphere (0 : ℂ) R ∩ {z : ℂ | 0 ≤ z.im}) ∪
    (fun x : ℝ => (x : ℂ)) '' Icc (-R) R

lemma fl4e_arg {r θ : ℝ} (hr : 0 < r) (hθ : θ ∈ Ioc (-π) π) :
    arg ((r : ℂ) * exp (θ * I)) = θ := by
  rw [exp_mul_I]
  exact arg_mul_cos_add_sin_mul_I hr hθ

lemma fl4e_norm {r : ℝ} (θ : ℝ) (hr : 0 ≤ r) : ‖(r : ℂ) * exp (θ * I)‖ = r := by
  rw [norm_mul, norm_exp_ofReal_mul_I, Complex.norm_of_nonneg hr, mul_one]

lemma fl4e_im (r θ : ℝ) : ((r : ℂ) * exp (θ * I)).im = r * Real.sin θ := by
  rw [im_ofReal_mul, exp_ofReal_mul_I_im]

lemma fl4e_injOn {r : ℝ} (hr : 0 < r) :
    InjOn (fun θ : ℝ => (r : ℂ) * exp (θ * I)) (Icc 0 π) := by
  intro a ha b hb h
  have e := congrArg arg h
  simp only at e
  rwa [fl4e_arg hr ⟨by linarith [Real.pi_pos, ha.1], ha.2⟩,
    fl4e_arg hr ⟨by linarith [Real.pi_pos, hb.1], hb.2⟩] at e

/-- The upper closed semicircle is the closed arc `[0, π]`. -/
lemma fl4e_semi_eq {R : ℝ} (hR : 0 < R) :
    sphere (0 : ℂ) R ∩ {z : ℂ | 0 ≤ z.im} = flClArc R 0 π := by
  ext z
  constructor
  · rintro ⟨hs, him⟩
    rw [mem_sphere, dist_zero_right] at hs
    refine ⟨arg z, ⟨arg_nonneg_iff.2 him, arg_le_pi z⟩, ?_⟩
    show (R : ℂ) * exp (arg z * I) = z
    rw [← hs]
    exact norm_mul_exp_arg_mul_I z
  · rintro ⟨θ, hθ, rfl⟩
    refine ⟨by rw [mem_sphere, dist_zero_right, fl4e_norm _ hR.le], ?_⟩
    show 0 ≤ ((R : ℂ) * exp (θ * I)).im
    rw [fl4e_im]
    exact mul_nonneg hR.le (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2)

lemma fl4e_closure_arc {ε α β : ℝ} (hαβ : α < β) :
    closure (flCircArc ε α β) = flClArc ε α β := by
  apply Subset.antisymm
  · exact closure_minimal (flCircArc_sub_clArc _ _ _)
      (isCompact_Icc.image (flClArc_cont ε)).isClosed
  · rw [flClArc, ← closure_Ioo hαβ.ne]
    exact image_closure_subset_closure_image (flClArc_cont ε)

section Frame

variable {γ : ℝ → ℂ} {t R ε α β : ℝ}

theorem fl4eE_isClosed (hγc : ContinuousOn γ (Icc 0 t)) : IsClosed (fl4eE γ t R ε α β) :=
  (((isCompact_Icc.image_of_continuousOn hγc).isClosed.union isClosed_closure).union
    (isClosed_sphere.inter (isClosed_le continuous_const continuous_im))).union
    (isCompact_Icc.image continuous_ofReal).isClosed

theorem fl4eE_sub_closedBall (hγlt : ∀ s ∈ Ico 0 t, ‖γ s‖ < R) (hγt : ‖γ t‖ = R)
    (hε : 0 < ε) (hεR : ε < R) : fl4eE γ t R ε α β ⊆ closedBall 0 R := by
  have hA : flCircArc ε α β ⊆ closedBall 0 R := by
    rintro _ ⟨θ, -, rfl⟩
    rw [mem_closedBall, dist_zero_right, fl4e_norm _ hε.le]
    exact hεR.le
  rintro z (((⟨s, hs, rfl⟩ | hz) | hz) | ⟨x, hx, rfl⟩)
  · rw [mem_closedBall, dist_zero_right]
    rcases hs.2.lt_or_eq with h | h
    · exact (hγlt s ⟨hs.1, h⟩).le
    · rw [h, hγt]
  · exact closure_minimal hA isClosed_closedBall hz
  · exact sphere_subset_closedBall hz.1
  · rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.2 hx

theorem fl4eE_ulc (ht : 0 ≤ t) (hγc : ContinuousOn γ (Icc 0 t)) (hR : 0 < R) (hαβ : α < β) :
    Topo.ULC (fl4eE γ t R ε α β) := by
  have hKc : IsCompact (γ '' Icc 0 t) := isCompact_Icc.image_of_continuousOn hγc
  have hAc : IsCompact (flClArc ε α β) := isCompact_Icc.image (flClArc_cont ε)
  have hSc : IsCompact (flClArc R 0 π) := isCompact_Icc.image (flClArc_cont R)
  rw [fl4eE, fl4e_closure_arc hαβ, fl4e_semi_eq hR]
  refine Topo.ULC.union_of_isCompact_of_isClosed ((hKc.union hAc).union hSc)
    (isCompact_Icc.image continuous_ofReal).isClosed ?_
    (flExist_ulc_image_Icc (by linarith) continuous_ofReal.continuousOn)
  refine Topo.ULC.union_of_isCompact_of_isClosed (hKc.union hAc) hSc.isClosed ?_
    (flExist_ulc_image_Icc Real.pi_pos.le (flClArc_cont R).continuousOn)
  exact Topo.ULC.union_of_isCompact_of_isClosed hKc hAc.isClosed (flExist_ulc_image_Icc ht hγc)
    (flExist_ulc_image_Icc hαβ.le (flClArc_cont ε).continuousOn)

end Frame

/-- Attaching an injective arc minus a point to a preconnected set `M` which contains every
end point of the arc other than the point. Own elementary proof. -/
lemma fl4e_arc_diff {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hi : InjOn f (Icc a b)) {M : Set ℂ} (hM : IsPreconnected M) (q : ℂ)
    (ha : f a ≠ q → f a ∈ M) (hb : f b ≠ q → f b ∈ M) :
    IsPreconnected (M ∪ (f '' Icc a b \ {q})) := by
  have step : ∀ N P : Set ℂ, IsPreconnected N → IsPreconnected P →
      (P = ∅ ∨ (N ∩ P).Nonempty) → IsPreconnected (N ∪ P) := by
    rintro N P hN hP (h | h)
    · rw [h, union_empty]; exact hN
    · exact hN.union' h hP
  by_cases hq : q ∈ f '' Icc a b
  · obtain ⟨s, hs, rfl⟩ := hq
    have h1 : Ico a s ⊆ Icc a b := fun u hu => ⟨hu.1, hu.2.le.trans hs.2⟩
    have h2 : Ioc s b ⊆ Icc a b := fun u hu => ⟨hs.1.trans hu.1.le, hu.2⟩
    have heq : f '' Icc a b \ {f s} = f '' Ico a s ∪ f '' Ioc s b := by
      ext z
      constructor
      · rintro ⟨⟨u, hu, rfl⟩, hne⟩
        have hus : u ≠ s := fun h => hne (h ▸ rfl)
        rcases lt_or_gt_of_ne hus with h | h
        · exact Or.inl ⟨u, ⟨hu.1, h⟩, rfl⟩
        · exact Or.inr ⟨u, ⟨h, hu.2⟩, rfl⟩
      · rintro (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
        · exact ⟨⟨u, h1 hu, rfl⟩, fun h => hu.2.ne (hi (h1 hu) hs h)⟩
        · exact ⟨⟨u, h2 hu, rfl⟩, fun h => hu.1.ne' (hi (h2 hu) hs h)⟩
    rw [heq, ← union_assoc]
    refine step _ _ (step _ _ hM (isPreconnected_Ico.image _ (hf.mono h1)) ?_)
      (isPreconnected_Ioc.image _ (hf.mono h2)) ?_
    · rcases hs.1.eq_or_lt with h | h
      · left; subst h; simp
      · right
        exact ⟨f a, ha (fun e => h.ne (hi ⟨le_rfl, hab⟩ hs e)), a, ⟨le_rfl, h⟩, rfl⟩
    · rcases hs.2.eq_or_lt with h | h
      · left; subst h; simp
      · right
        exact ⟨f b, Or.inl (hb (fun e => h.ne' (hi ⟨hab, le_rfl⟩ hs e))), b, ⟨h, le_rfl⟩, rfl⟩
  · rw [sdiff_singleton_eq_self hq]
    exact hM.union (f a) (ha fun e => hq ⟨a, ⟨le_rfl, hab⟩, e⟩) ⟨a, ⟨le_rfl, hab⟩, rfl⟩
      (isPreconnected_Icc.image _ hf)

lemma fl4e_S0 (R : ℝ) : (R : ℂ) * exp ((0 : ℝ) * I) = (R : ℂ) := by simp

lemma fl4e_Spi (R : ℝ) : (R : ℂ) * exp ((π : ℝ) * I) = -(R : ℂ) := by
  rw [exp_pi_mul_I]; ring

lemma fl4e_seg_neg (R : ℝ) : (fun x : ℝ => (x : ℂ)) (-R) = -(R : ℂ) := by simp

/-- The boundary `C_R⁺ ∪ [-R, R]` of the closed upper half-disc minus any point is
preconnected. Own elementary proof. -/
theorem fl4e_J_diff {R : ℝ} (hR : 0 < R) (q : ℂ) :
    IsPreconnected ((flClArc R 0 π ∪ (fun x : ℝ => (x : ℂ)) '' Icc (-R) R) \ {q}) := by
  set f : ℝ → ℂ := fun x => (x : ℂ) with hf
  set g : ℝ → ℂ := fun θ => (R : ℂ) * exp (θ * I) with hg
  set S := flClArc R 0 π
  set seg := f '' Icc (-R) R
  have hRR : -R ≤ R := by linarith
  have hfc : ContinuousOn f (Icc (-R) R) := continuous_ofReal.continuousOn
  have hfi : InjOn f (Icc (-R) R) := ofReal_injective.injOn
  have hgc : ContinuousOn g (Icc 0 π) := (flClArc_cont R).continuousOn
  have hgi : InjOn g (Icc 0 π) := fl4e_injOn hR
  have hSp : IsPreconnected S := isPreconnected_Icc.image _ hgc
  have hsegp : IsPreconnected seg := isPreconnected_Icc.image _ hfc
  have hRS : (R : ℂ) ∈ S := ⟨0, ⟨le_rfl, Real.pi_pos.le⟩, fl4e_S0 R⟩
  have hnRS : -(R : ℂ) ∈ S := ⟨π, ⟨Real.pi_pos.le, le_rfl⟩, fl4e_Spi R⟩
  have hRseg : (R : ℂ) ∈ seg := ⟨R, ⟨hRR, le_rfl⟩, rfl⟩
  have hnRseg : -(R : ℂ) ∈ seg := ⟨-R, ⟨le_rfl, hRR⟩, fl4e_seg_neg R⟩
  have hg0 : g 0 = R := fl4e_S0 R
  have hgπ : g π = -R := fl4e_Spi R
  have hfR : f R = R := rfl
  have hfnR : f (-R) = -R := fl4e_seg_neg R
  have fin : ∀ M : Set ℂ, IsPreconnected M → M ⊆ (S ∪ seg) \ {q} →
      (S ∪ seg) \ {q} ⊆ M → IsPreconnected ((S ∪ seg) \ {q}) := fun M hM h1 h2 =>
    (Subset.antisymm h1 h2) ▸ hM
  by_cases hqS : q ∈ S
  · by_cases hqseg : q ∈ seg
    · -- `q = ±R`
      obtain ⟨x, hx, rfl⟩ := hqseg
      obtain ⟨θ, hθ, hθe⟩ := hqS
      have hxR : |x| = R := by
        have := fl4e_norm θ hR.le
        rw [show (R : ℂ) * exp (θ * I) = f x from hθe, hf, Complex.norm_real,
          Real.norm_eq_abs] at this
        exact this
      rcases abs_eq hR.le |>.1 hxR with h | h
      · subst h
        have hA := fl4e_arc_diff (f := g) Real.pi_pos.le hgc hgi (isPreconnected_singleton (x := -(x : ℂ)))
          (x : ℂ) (fun h => absurd hg0 h) (fun _ => by rw [hgπ]; rfl)
        have hB := fl4e_arc_diff (f := f) hRR hfc hfi hA (x : ℂ)
          (fun h => Or.inl (by rw [hfnR]; rfl)) (fun h => absurd hfR h)
        refine fin _ hB ?_ ?_
        · rintro z ((hz | ⟨hz, hzq⟩) | ⟨hz, hzq⟩)
          · rw [mem_singleton_iff.1 hz]
            exact ⟨Or.inl hnRS, fun h => by
              have := congrArg Complex.re (mem_singleton_iff.1 h); simp [hf] at this; linarith⟩
          · exact ⟨Or.inl hz, hzq⟩
          · exact ⟨Or.inr hz, hzq⟩
        · rintro z ⟨hz | hz, hzq⟩
          · exact Or.inl (Or.inr ⟨hz, hzq⟩)
          · exact Or.inr ⟨hz, hzq⟩
      · have hx : x = -R := h
        subst hx
        have hA := fl4e_arc_diff (f := g) Real.pi_pos.le hgc hgi (isPreconnected_singleton (x := (R : ℂ)))
          (f (-R)) (fun _ => by rw [hg0]; rfl) (fun h => absurd (hgπ.trans hfnR.symm) h)
        have hB := fl4e_arc_diff (f := f) hRR hfc hfi hA (f (-R))
          (fun h => absurd rfl h) (fun _ => Or.inl (by rw [hfR]; rfl))
        refine fin _ hB ?_ ?_
        · rintro z ((hz | ⟨hz, hzq⟩) | ⟨hz, hzq⟩)
          · rw [mem_singleton_iff.1 hz]
            exact ⟨Or.inl hRS, fun h => by
              have := congrArg Complex.re (mem_singleton_iff.1 h); simp [hf] at this; linarith⟩
          · exact ⟨Or.inl hz, hzq⟩
          · exact ⟨Or.inr hz, hzq⟩
        · rintro z ⟨hz | hz, hzq⟩
          · exact Or.inl (Or.inr ⟨hz, hzq⟩)
          · exact Or.inr ⟨hz, hzq⟩
    · have hB := fl4e_arc_diff (f := g) Real.pi_pos.le hgc hgi hsegp q
        (fun _ => by rw [hg0]; exact hRseg) (fun _ => by rw [hgπ]; exact hnRseg)
      refine fin _ hB ?_ ?_
      · rintro z (hz | ⟨hz, hzq⟩)
        · exact ⟨Or.inr hz, fun h => hqseg (mem_singleton_iff.1 h ▸ hz)⟩
        · exact ⟨Or.inl hz, hzq⟩
      · rintro z ⟨hz | hz, hzq⟩
        · exact Or.inr ⟨hz, hzq⟩
        · exact Or.inl hz
  · have hB := fl4e_arc_diff (f := f) hRR hfc hfi hSp q
      (fun _ => by rw [hfnR]; exact hnRS) (fun _ => by rw [hfR]; exact hRS)
    refine fin _ hB ?_ ?_
    · rintro z (hz | ⟨hz, hzq⟩)
      · exact ⟨Or.inl hz, fun h => hqS (mem_singleton_iff.1 h ▸ hz)⟩
      · exact ⟨Or.inr hz, hzq⟩
    · rintro z ⟨hz | hz, hzq⟩
      · exact Or.inl hz
      · exact Or.inr ⟨hz, hzq⟩

end FieldLawler
end QuantumZipper
