import QuantumZipper.Proofs.Zipper.FieldLawler4WdOuter

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL4-WD (iii): a boundary point of `Wd` off both arcs

Task FL4-WD, datum (iii) for the Möbius normalisation of `fl3Wd_excR_symm`:
`fl4wd_bdry_point` gives `p ∈ ∂Wd` with `ε < ‖p‖ < R`, hence `p ∉ closure ηD ⊆ C_ε` and
`p ∉ closure (∂Wd ∩ C_R) ⊆ C_R`; moreover `p ∈ K_t ∪ ℝ`. It is found next to a point of
`∂Wd ∩ C_R` that is also a limit of `B(0,R) \ Wd` (the tip, `R` or `-R`; if the `C_R` piece
contains a chart point, the whole sub-arc of `C_R ∩ ℍ` between the tip and `±R` belongs to it).
Own elementary argument.
-/

noncomputable section

open Set Filter Metric Complex
open scoped Topology Real

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

variable {W : ℝ → ℝ} {t : ℝ} {F : ℂ → ℂ}

lemma fl4wd_real_closure {R ε α β : ℝ} (hR : 0 < R) (p₀ : ℂ) {c : ℂ}
    (hc0 : c.im = 0) (hcR : ‖c‖ = R) : c ∈ closure (ball 0 R \ fl4Wd W t R ε α β p₀) := by
  have ht : Tendsto (fun s : ℝ => ((1 - s : ℝ) : ℂ) * c) (𝓝[>] 0) (𝓝 c) := by
    have : Tendsto (fun s : ℝ => ((1 - s : ℝ) : ℂ) * c) (𝓝 0) (𝓝 (((1 - 0 : ℝ) : ℂ) * c)) :=
      ((continuous_ofReal.comp (continuous_const.sub continuous_id)).mul
        continuous_const).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsGT one_pos] with s hs
  refine ⟨?_, fun hW => ?_⟩
  · rw [mem_ball_zero_iff, norm_mul, hcR, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith [hs.2])]
    nlinarith [hs.1]
  · have := (fl4wd_subset_D hW).1
    change 0 < (((1 - s : ℝ) : ℂ) * c).im at this
    simp [hc0] at this

lemma fl4wd_tip_closure (hc : SideCtx W t F) {R ε α β : ℝ}
    (hlt : ∀ s ∈ Ico 0 t, ‖trace W s‖ < R) (p₀ : ℂ) :
    trace W t ∈ closure (ball 0 R \ fl4Wd W t R ε α β p₀) := by
  have htc : Tendsto (trace W) (𝓝[<] t) (𝓝 (trace W t)) := by
    rw [← nhdsWithin_Ioo_eq_nhdsLT hc.tpos]
    exact (hc.trCont t (right_mem_Icc.2 hc.tpos.le)).tendsto.mono_left
      (nhdsWithin_mono _ Ioo_subset_Icc_self)
  refine mem_closure_of_tendsto htc ?_
  filter_upwards [Ioo_mem_nhdsLT hc.tpos] with s hs
  refine ⟨mem_ball_zero_iff.2 (hlt s ⟨hs.1.le, hs.2⟩), fun hsW => ?_⟩
  exact (fl4wd_subset_D hsW).2 (by rw [hc.hull]; exact ⟨s, ⟨hs.1, hs.2.le⟩, rfl⟩)

lemma fl4_chart_im {R : ℝ} (θ : ℝ) : (fl3Chart R θ).im = R * Real.sin θ := by
  simp [fl3Chart, Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_re]

/-- **Chaining along `C_R`.** If an open interval of angles in `(0, π)` avoids the tip's angle
and meets `J`, it lies in `J`. -/
lemma fl4wd_interval_subset (hc : SideCtx W t F) {R ε α β : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (hlt : ∀ s ∈ Ico 0 t, ‖trace W s‖ < R) (p₀ : ℂ) {a' b' θ : ℝ}
    (hI : Ioo a' b' ⊆ Ioo 0 π) (htip : arg (trace W t) ∉ Ioo a' b') (hθ : θ ∈ Ioo a' b')
    (hθJ : θ ∈ fl4WdJ W t R ε α β p₀) : Ioo a' b' ⊆ fl4WdJ W t R ε α β p₀ := by
  have hR : 0 < R := hε.trans hεR
  set g : ℝ → ℂ := fun θ => fl3Chart R θ
  have hg : Continuous g := (fl4_chart_continuous R).comp continuous_ofReal
  refine isPreconnected_Ioo.subset_of_closure_inter_subset (fl4WdJ_isOpen R ε α β p₀)
    ⟨θ, hθ, hθJ⟩ ?_
  rintro θ' ⟨hθ'1, hθ'2⟩
  have hsub : g '' fl4WdJ W t R ε α β p₀ ⊆ closure (fl4Wd W t R ε α β p₀) := by
    rintro _ ⟨φ, hφ, rfl⟩
    exact ((fl4wd_outer_eq hc hε hεR hlt p₀).1 ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩).1.1
  have hx : g θ' ∈ closure (fl4Wd W t R ε α β p₀) := by
    have := image_closure_subset_closure_image hg ⟨θ', hθ'1, rfl⟩
    exact closure_minimal hsub isClosed_closure this
  have hθ'I := hI hθ'2
  have hxR : ‖g θ'‖ = R := by
    simp only [g]; rw [fl4_chart_norm hR.le]; simp
  have him : 0 < (g θ').im := by
    simp only [g]; rw [fl4_chart_im]
    exact mul_pos hR (Real.sin_pos_of_pos_of_lt_pi hθ'I.1 hθ'I.2)
  have harg : arg (g θ') = θ' := fl4_chart_arg hR hθ'I
  have hne : g θ' ≠ trace W t := fun e => htip (by rw [← e, harg]; exact hθ'2)
  have := (fl4wd_mem_J hc hε hεR hlt p₀ hx hxR him hne).1
  rwa [harg] at this

/-- **(iii)** A frontier point of `Wd` strictly between `C_ε` and `C_R`; it lies in `K_t ∪ ℝ`. -/
theorem fl4wd_bdry_point (hc : SideCtx W t F) {R ε α β : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (hlt : ∀ s ∈ Ico 0 t, ‖trace W s‖ < R) (hnorm : ‖trace W t‖ = R) (hH : trace W t ∈ H)
    {η' : ℝ → ℂ} (hη : IsCrosscutH η') {a b : ℝ} (ha : Tendsto η' (𝓝[>] 0) (𝓝 (a : ℂ)))
    (hb : Tendsto η' (𝓝[<] 1) (𝓝 (b : ℂ))) (hab : a < b)
    (hηD : fwdMapInv W t '' arcH η' = flCircArc ε α β) {p₀ : ℂ}
    (hp : p₀ ∈ fl4WdDom W t R ε α β) (hpU : fwdMap W t p₀ ∈ hullComp η') :
    ∃ p ∈ frontier (fl4Wd W t R ε α β p₀), ε < ‖p‖ ∧ ‖p‖ < R ∧
      p ∈ fwdHull W t ∪ range ofReal := by
  have hR : 0 < R := hε.trans hεR
  set Wd := fl4Wd W t R ε α β p₀
  have hcl : closure Wd ⊆ closedBall 0 R :=
    closure_minimal (fl4wd_subset_ball.trans ball_subset_closedBall) isClosed_closedBall
  -- a point of `C_R ∩ closure Wd` that is a limit of `B(0,R) \ Wd`
  obtain ⟨c, hcW, hcB, hcR⟩ : ∃ c, c ∈ closure Wd ∧ c ∈ closure (ball 0 R \ Wd) ∧ ‖c‖ = R := by
    obtain ⟨x, hxA⟩ := fl4wd_outer_nonempty hc hη ha hb hab hηD hp hpU
    have hxR : ‖x‖ = R := by simpa using hxA.2
    by_cases hxt : x = trace W t
    · exact ⟨x, hxA.1.1, hxt ▸ fl4wd_tip_closure hc hlt p₀, hxR⟩
    rcases (fl4wd_outer_eq hc hε hεR hlt p₀).2 hxA with hx' | hx3
    · obtain ⟨_, ⟨θ, hθJ, rfl⟩, rfl⟩ := hx'
      set θt := arg (trace W t)
      have hθI := hθJ.1
      have hθt : θt ∈ Ioo 0 π := by
        have := hH.out
        exact ⟨lt_of_le_of_ne (arg_nonneg_iff.2 this.le) fun e => by
          have := (arg_eq_zero_iff.1 e.symm).2; linarith, arg_lt_pi_iff.2 (Or.inr this.ne')⟩
      have hne : θ ≠ θt := fun e => hxt (by
        rw [e]; simp only [θt]; rw [fl3Chart, ← hnorm]; exact norm_mul_exp_arg_mul_I _)
      set g : ℝ → ℂ := fun θ => fl3Chart R θ
      have hg : Continuous g := (fl4_chart_continuous R).comp continuous_ofReal
      have hJW : ∀ φ ∈ fl4WdJ W t R ε α β p₀, g φ ∈ closure Wd := fun φ hφ =>
        ((fl4wd_outer_eq hc hε hεR hlt p₀).1 ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩).1.1
      rcases lt_or_gt_of_ne hne with h | h
      · have hsub := fl4wd_interval_subset hc hε hεR hlt p₀ (a' := 0) (b' := θt)
          (fun φ hφ => ⟨hφ.1, hφ.2.trans hθt.2⟩) (fun h' => lt_irrefl _ h'.2) ⟨hθI.1, h⟩ hθJ
        refine ⟨R, ?_, fl4wd_real_closure hR p₀ (c := (R : ℂ)) (by simp) (by simp [hR.le]),
          by simp [hR.le]⟩
        have ht : Tendsto g (𝓝[>] 0) (𝓝 (g 0)) := hg.continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds
        have h0 : g 0 = R := by simp [g, fl3Chart]
        rw [h0] at ht
        rw [← closure_closure (s := Wd)]
        refine mem_closure_of_tendsto ht ?_
        filter_upwards [Ioo_mem_nhdsGT hθt.1] with φ hφ
        exact hJW φ (hsub hφ)
      · have hsub := fl4wd_interval_subset hc hε hεR hlt p₀ (a' := θt) (b' := π)
          (fun φ hφ => ⟨hθt.1.trans hφ.1, hφ.2⟩) (fun h' => lt_irrefl _ h'.1) ⟨h, hθI.2⟩ hθJ
        refine ⟨-R, ?_, fl4wd_real_closure hR p₀ (c := -(R : ℂ)) (by simp) (by simp [hR.le]),
          by simp [hR.le]⟩
        have ht : Tendsto g (𝓝[<] π) (𝓝 (g π)) := hg.continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds
        have h0 : g π = -R := by simp [g, fl3Chart, exp_pi_mul_I]
        rw [h0] at ht
        rw [← closure_closure (s := Wd)]
        refine mem_closure_of_tendsto ht ?_
        filter_upwards [Ioo_mem_nhdsLT hθt.2] with φ hφ
        exact hJW φ (hsub hφ)
    · have hx3' : x = (R : ℂ) ∨ x = -(R : ℂ) := by
        simp only [mem_insert_iff, mem_singleton_iff] at hx3
        tauto
      refine ⟨x, hxA.1.1, fl4wd_real_closure hR p₀ ?_ hxR, hxR⟩
      rcases hx3' with rfl | rfl <;> simp
  have hfr := fl4_closure_frontier_of (fl4wd_open hc) fl4wd_subset_ball hcW hcB
  obtain ⟨y, ⟨hy, hys⟩, hyd⟩ := Metric.mem_closure_iff.1 hfr (R - ε) (by linarith)
  have hyR : ‖y‖ < R := by
    have := hcl hy.1
    rw [mem_closedBall_zero_iff] at this
    exact lt_of_le_of_ne this fun e => hys (by simpa using e)
  have hyε : ε < ‖y‖ := by
    have := norm_sub_norm_le c y
    rw [← dist_eq_norm] at this
    linarith
  refine ⟨y, hy, hyε, hyR, ?_⟩
  rcases fl4wd_frontier_subset hc hε ⟨hy, hys⟩ with h | h
  · exact h
  · exact absurd (by simpa using h : ‖y‖ = ε) hyε.ne'

end FieldLawler
end QuantumZipper
