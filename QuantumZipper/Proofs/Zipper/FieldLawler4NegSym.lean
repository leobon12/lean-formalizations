import QuantumZipper.Proofs.Zipper.FieldLawler3Asm1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL4-NEG (part 2): the first symmetry step for NEGATIVE feet, `ℰ(η, (0, N)) = ℰ((0, N), η)`

Mirror of `FieldLawler3Asm1.lean` for a crosscut `η` with feet `a < b < 0` and the real piece
`(0, N)` of `∂H_η`: `fl4neg_first_symm` states `excR h (0, N) = excR (G ∘ ψ) J`.

Source: Field–Lawler, *Escape probability and transience for SLE*, EJP 20 (2015), pp. 7 and 9
(symmetry of the excursion measure), via Lawler, *Conformally Invariant Processes in the Plane*,
Prop. 5.8, p. 105 (`fl3Sym_excR_symm'`). The half-disk input `fl4neg_halfDisk` is
`flExc_halfDisk` transported by the scaling `z ↦ z/(−a)` (`flSim 1 (−a)`), which sends the foot
`a` to `−1`. Own elementary glue as in FieldLawler3Asm1 (cost rule of AGENT_GUIDE).
-/

noncomputable section

open MeasureTheory Filter Set Metric Complex
open scoped Topology

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

/-- `flSim 1 m` scales distances by `1/m`. -/
lemma fl4neg_dist_flSim {m : ℝ} (hm : 0 < m) (z w : ℂ) :
    dist (flSim 1 m z) (flSim 1 m w) = dist z w / m := by
  rw [Complex.dist_eq_re_im, Complex.dist_eq_re_im, (flSim_re_im _ _ z).1, (flSim_re_im _ _ z).2,
    (flSim_re_im _ _ w).1, (flSim_re_im _ _ w).2]
  have e : (1 * z.re / m - 1 * w.re / m) ^ 2 + (z.im / m - w.im / m) ^ 2 =
      ((z.re - w.re) ^ 2 + (z.im - w.im) ^ 2) / m ^ 2 := by
    field_simp
  rw [e, Real.sqrt_div' _ (sq_nonneg m), Real.sqrt_sq hm.le]

/-- **Half-disks over `x ≥ 0` lie in `H_η`** when the feet `a < b < 0` of `η` are negative; the
real points of the half-disk are frontier points of `H_η` off `closure η`. -/
theorem fl4neg_halfDisk {η : ℝ → ℂ} (hη : IsCrosscutH η) {a b : ℝ}
    (ha : Tendsto η (𝓝[>] 0) (𝓝 (a : ℂ))) (hb : Tendsto η (𝓝[<] 1) (𝓝 (b : ℂ)))
    (hb0 : b < 0) (hab : a < b) {x : ℝ} (hx : 0 ≤ x) :
    ∃ r > 0, H ∩ ball (x : ℂ) r ⊆ hullComp η ∧
      ∀ w ∈ ball (x : ℂ) r, w.im = 0 → w ∉ closure (arcH η) ∧ w ∈ frontier (hullComp η) := by
  have hm : 0 < -a := by linarith
  have hσ : (1 : ℝ) = 1 ∨ (1 : ℝ) = -1 := Or.inl rfl
  set e := flSimHomeo 1 (-a) (fl_sigma_sq hσ) hm.ne' with he
  have heq : ∀ z, e z = flSim 1 (-a) z := fun _ => rfl
  have hη' := flSim_crosscut hσ hm hη
  have h0' : Tendsto (fun t => e (η t)) (𝓝[>] 0) (𝓝 (-1 : ℂ)) := by
    have := (e.continuous.tendsto _).comp ha
    rwa [show e (a : ℂ) = -1 by
      rw [heq, flSim_real, show (1 * a / -a : ℝ) = -1 by
        rw [one_mul, div_neg, div_self (show a ≠ 0 by linarith)]]
      push_cast; ring] at this
  have h1' : Tendsto (fun t => e (η t)) (𝓝[<] 1) (𝓝 (((1 * b / -a : ℝ)) : ℂ)) := by
    have := (e.continuous.tendsto _).comp hb
    rwa [show e (b : ℂ) = ((1 * b / -a : ℝ) : ℂ) from flSim_real _ _ b] at this
  have hb' : 1 * b / -a < 0 := div_neg_of_neg_of_pos (by linarith) hm
  have hx' : 0 ≤ 1 * x / -a := div_nonneg (by linarith) hm.le
  obtain ⟨r', hr', hsub, hnot⟩ := flExc_halfDisk hη' h0' h1' hb' hx'
  have hex : e (x : ℂ) = ((1 * x / -a : ℝ) : ℂ) := flSim_real _ _ x
  have hball : ∀ z ∈ ball (x : ℂ) (-a * r'), e z ∈ ball ((1 * x / -a : ℝ) : ℂ) r' := by
    intro z hz
    rw [mem_ball] at hz ⊢
    rw [← hex, heq, heq, fl4neg_dist_flSim hm, div_lt_iff₀ hm]
    linarith
  have hsub' : H ∩ ball (x : ℂ) (-a * r') ⊆ hullComp η := by
    rintro z ⟨hzH, hzB⟩
    have hmem := hsub ⟨(flSim_mem_H hm z).2 hzH, hball z hzB⟩
    rw [flSim_hullComp hσ hm η] at hmem
    obtain ⟨z0, hz0, hze⟩ := hmem
    rwa [e.injective hze] at hz0
  refine ⟨-a * r', mul_pos hm hr', hsub', fun w hw hwim => ⟨?_, ?_⟩⟩
  · intro hwc
    refine hnot (e w) (hball w hw) (by rw [heq, (flSim_re_im _ _ w).2, hwim, zero_div]) ?_
    rw [flSim_arcH hσ hm η, ← e.image_closure]
    exact ⟨w, hwc, rfl⟩
  · refine ⟨?_, fun hint => ?_⟩
    · have hwH : w ∈ closure H := by
        rw [show H = {z : ℂ | 0 < z.im} from rfl, Complex.closure_setOfPred_lt_im]
        exact le_of_eq hwim.symm
      have := isOpen_ball.inter_closure ⟨hw, hwH⟩
      rw [inter_comm] at this
      exact closure_mono hsub' this
    · have := (interior_subset hint).1.1
      change 0 < w.im at this
      linarith

/-- The real segment `(0, N)` is an analytic boundary arc of `H_η` with chart `id`. -/
theorem fl4neg_arc_id {η : ℝ → ℂ} (hη : IsCrosscutH η) {a b : ℝ}
    (ha : Tendsto η (𝓝[>] 0) (𝓝 (a : ℂ))) (hb : Tendsto η (𝓝[<] 1) (𝓝 (b : ℂ)))
    (hb0 : b < 0) (hab : a < b) (N : ℝ) : FL3Arc (hullComp η) id (Ioo 0 N) where
  meas := measurableSet_Ioo
  chart x hx := by
    obtain ⟨r, hr, hsub, hfr⟩ := fl4neg_halfDisk hη ha hb hb0 hab hx.1.le
    exact ⟨r, hr, differentiableOn_id, fun z hz => hsub hz, fun z hz hzim => (hfr z hz hzim).2⟩
  inj x _ y _ h := Complex.ofReal_injective h

/-- **FL4-NEG: the first symmetry step for negative feet** (Field–Lawler, EJP 20 (2015), pp. 7 and 9, via
Lawler, *Conformally Invariant Processes in the Plane*, Prop. 5.8, p. 105). -/
theorem fl4neg_first_symm {η : ℝ → ℂ} (hη : IsCrosscutH η) {a b N : ℝ}
    (ha : Tendsto η (𝓝[>] 0) (𝓝 (a : ℂ))) (hb : Tendsto η (𝓝[<] 1) (𝓝 (b : ℂ)))
    (hb0 : b < 0) (hab : a < b) (hN : 0 < N)
    {G h : ℂ → ℝ} (hG : IsHarmMeas (hullComp η) (((↑) : ℝ → ℂ) '' Ioo 0 N) G)
    (hh : IsHarmMeas (hullComp η) (arcH η) h)
    {ψ : ℂ → ℂ} {J : Set ℝ} (hψ : FL3Arc (hullComp η) ψ J)
    (hψJ : ψ '' (((↑) : ℝ → ℂ) '' J) = arcH η) :
    excR h (Ioo 0 N) = excR (G ∘ ψ) J := by
  obtain ⟨F, α, β, hF, hαβ, -, -, hIoo, hrest⟩ := fl3u_FL3Unif_pieces hη ha hb hab
  set g : ℝ → ℝ := fun x => (F (x : ℂ)).re with hg
  have hpt : ∀ x ∈ Icc 0 N, ((x : ℂ) ∈ frontier (hullComp η)) ∧ (x : ℂ) ∉ closure (arcH η) :=
    fun x hx => by
      obtain ⟨r, hr, -, hfr⟩ := fl4neg_halfDisk hη ha hb hb0 hab hx.1
      exact ⟨(hfr _ (mem_ball_self hr) (by simp)).2, (hfr _ (mem_ball_self hr) (by simp)).1⟩
  have havoid : ∀ x ∈ Icc 0 N, g x < α ∨ β < g x := fun x hx =>
    (hrest _ (hpt x hx).1 (hpt x hx).2).2.2
  have hcont : ContinuousOn g (Icc 0 N) :=
    Complex.continuous_re.comp_continuousOn (hF.cont.comp continuous_ofReal.continuousOn
      fun x hx => frontier_subset_closure (hpt x hx).1)
  have hreal : ∀ z ∈ frontier (hullComp η), F z = (((F z).re : ℝ) : ℂ) := fun z hz =>
    Complex.ext (by simp) (by simp [hF.bdry_real z hz])
  have hinj : InjOn g (Icc 0 N) := fun x hx y hy hxy => by
    have := hF.bdry_inj (hpt x hx).1 (hpt y hy).1
      (by rw [hreal _ (hpt x hx).1, hreal _ (hpt y hy).1]; exact congrArg _ hxy)
    exact Complex.ofReal_injective this
  have hN0 : 0 ≤ N := by linarith
  have hsub : ∀ t ∈ g '' Ioo 0 N, t < α ∨ β < t := by
    rintro _ ⟨x, hx, rfl⟩
    exact havoid x (Ioo_subset_Icc_self hx)
  have hA := fl4neg_arc_id hη ha hb hb0 hab N
  have hIB : (fun x : ℝ => (F (ψ x)).re) '' J = Ioo α β := by
    rw [← hIoo, ← hψJ, image_image, image_image]
  have hωA : IsHarmMeas (hullComp η) (id '' (((↑) : ℝ → ℂ) '' Ioo 0 N)) G := by
    rwa [image_id]
  have hωB : IsHarmMeas (hullComp η) (ψ '' (((↑) : ℝ → ℂ) '' J)) h := by rwa [hψJ]
  have hlt : 0 < N := hN
  have hIcc0 : (0 : ℝ) ∈ Icc 0 N := ⟨le_rfl, hN0⟩
  have hIccN : (N : ℝ) ∈ Icc 0 N := ⟨hN0, le_rfl⟩
  rcases hcont.strictMonoOn_of_injOn_Icc' hN0 hinj with hmono | hmono
  · have hI := hcont.image_Ioo_of_strictMonoOn hN0 hmono
    have hcd : g 0 < g N := hmono hIcc0 hIccN hlt
    have := fl3Sym_excR_symm' hF hA hψ hcd hαβ
      (fl3a1_side hαβ (havoid _ hIcc0) (havoid _ hIccN) (hI ▸ hsub)) hI hIB hωA hωB
    simpa using this
  · have hI := hcont.image_Ioo_of_strictAntiOn hN0 hmono
    have hcd : g N < g 0 := hmono hIcc0 hIccN hlt
    have := fl3Sym_excR_symm' hF hA hψ hcd hαβ
      (fl3a1_side hαβ (havoid _ hIccN) (havoid _ hIcc0) (hI ▸ hsub)) hI hIB hωA hωB
    simpa using this

end FieldLawler
end QuantumZipper
