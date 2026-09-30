import QuantumZipper.Proofs.Zipper.FieldLawler3Sym
import QuantumZipper.Proofs.Zipper.FieldLawler3UnifF
import QuantumZipper.Proofs.Zipper.FieldLawlerCoverExc
import QuantumZipper.Proofs.Zipper.FieldLawlerSubExcGeo

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL3-ASM1: the first symmetry step `ℰ_{H_η}(η, (−N, 0)) = ℰ_{H_η}((−N, 0), η)`

Field–Lawler, *Escape probability and transience for SLE*, EJP 20 (2015), p. 7 and p. 9: the
excursion measure between the boundary arc `η` and the real piece `ℝ₋` of `∂H_η` is symmetric
(`E_H(η, R₋) ≤ E_H(η, γ̃)` is applied after this symmetry). Here, for `(−N, 0)` and a chart `ψ`
of `η` over `J`, `fl3_first_symm` states `excR h (−N, 0) = excR (G ∘ ψ) J`, where `h`, `G` are
the harmonic measures of `η` and of `(−N, 0)` in `H_η`.

Proof: `fl3Sym_excR_symm'` (Lawler, *Conformally Invariant Processes in the Plane*, Prop. 5.8,
p. 105) with the uniformization of `fl3u_FL3Unif_pieces`. The inputs:
* `fl3a1_halfDisk`: half-disks over real `x ≤ 0` lie in `H_η` when the feet of `η` are positive
  (`flExc_halfDisk` transported by the reflection-scaling `z ↦ −z̄/a`, `flSim (−1) a`);
* `Re F` is continuous and injective on `[−N, 0]` (real frontier points), hence strictly
  monotone (mathlib `ContinuousOn.strictMonoOn_of_injOn_Icc'`), and its image avoids `[α, β]`.
Own elementary glue (cost rule of AGENT_GUIDE).
-/

noncomputable section

open MeasureTheory Filter Set Metric Complex
open scoped Topology

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

/-- `flSim σ m` scales distances by `1/m`. -/
lemma fl3a1_dist_flSim {m : ℝ} (hm : 0 < m) (z w : ℂ) :
    dist (flSim (-1) m z) (flSim (-1) m w) = dist z w / m := by
  rw [Complex.dist_eq_re_im, Complex.dist_eq_re_im, (flSim_re_im _ _ z).1, (flSim_re_im _ _ z).2,
    (flSim_re_im _ _ w).1, (flSim_re_im _ _ w).2]
  have e : (-1 * z.re / m - -1 * w.re / m) ^ 2 + (z.im / m - w.im / m) ^ 2 =
      ((z.re - w.re) ^ 2 + (z.im - w.im) ^ 2) / m ^ 2 := by
    field_simp; ring
  rw [e, Real.sqrt_div' _ (sq_nonneg m), Real.sqrt_sq hm.le]

/-- **Half-disks over `x ≤ 0` lie in `H_η`** when the feet `0 < a < b` of `η` are positive; the
real points of the half-disk are frontier points of `H_η` off `closure η`. -/
theorem fl3a1_halfDisk {η : ℝ → ℂ} (hη : IsCrosscutH η) {a b : ℝ}
    (ha : Tendsto η (𝓝[>] 0) (𝓝 (a : ℂ))) (hb : Tendsto η (𝓝[<] 1) (𝓝 (b : ℂ)))
    (ha0 : 0 < a) (hab : a < b) {x : ℝ} (hx : x ≤ 0) :
    ∃ r > 0, H ∩ ball (x : ℂ) r ⊆ hullComp η ∧
      ∀ w ∈ ball (x : ℂ) r, w.im = 0 → w ∉ closure (arcH η) ∧ w ∈ frontier (hullComp η) := by
  have hσ : (-1 : ℝ) = 1 ∨ (-1 : ℝ) = -1 := Or.inr rfl
  set e := flSimHomeo (-1) a (fl_sigma_sq hσ) ha0.ne' with he
  have heq : ∀ z, e z = flSim (-1) a z := fun _ => rfl
  have hη' := flSim_crosscut hσ ha0 hη
  have h0' : Tendsto (fun t => e (η t)) (𝓝[>] 0) (𝓝 (-1 : ℂ)) := by
    have := (e.continuous.tendsto _).comp ha
    rwa [show e (a : ℂ) = -1 by
      rw [heq, flSim_real]; push_cast
      rw [mul_div_assoc, div_self (Complex.ofReal_ne_zero.2 ha0.ne'), mul_one]] at this
  have h1' : Tendsto (fun t => e (η t)) (𝓝[<] 1) (𝓝 (((-1 * b / a : ℝ)) : ℂ)) := by
    have := (e.continuous.tendsto _).comp hb
    rwa [show e (b : ℂ) = ((-1 * b / a : ℝ) : ℂ) from flSim_real _ _ b] at this
  have hb' : -1 * b / a < 0 := div_neg_of_neg_of_pos (by linarith) ha0
  have hx' : 0 ≤ -1 * x / a := div_nonneg (by linarith) ha0.le
  obtain ⟨r', hr', hsub, hnot⟩ := flExc_halfDisk hη' h0' h1' hb' hx'
  have hex : e (x : ℂ) = ((-1 * x / a : ℝ) : ℂ) := flSim_real _ _ x
  have hball : ∀ z ∈ ball (x : ℂ) (a * r'), e z ∈ ball ((-1 * x / a : ℝ) : ℂ) r' := by
    intro z hz
    rw [mem_ball] at hz ⊢
    rw [← hex, heq, heq, fl3a1_dist_flSim ha0, div_lt_iff₀ ha0]
    linarith
  have hsub' : H ∩ ball (x : ℂ) (a * r') ⊆ hullComp η := by
    rintro z ⟨hzH, hzB⟩
    have hmem := hsub ⟨(flSim_mem_H ha0 z).2 hzH, hball z hzB⟩
    rw [flSim_hullComp hσ ha0 η] at hmem
    obtain ⟨z0, hz0, hze⟩ := hmem
    rwa [e.injective hze] at hz0
  refine ⟨a * r', mul_pos ha0 hr', hsub', fun w hw hwim => ⟨?_, ?_⟩⟩
  · intro hwc
    refine hnot (e w) (hball w hw) (by rw [heq, (flSim_re_im _ _ w).2, hwim, zero_div]) ?_
    rw [flSim_arcH hσ ha0 η, ← e.image_closure]
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

/-- The real segment `(−N, 0)` is an analytic boundary arc of `H_η` with chart `id`. -/
theorem fl3a1_arc_id {η : ℝ → ℂ} (hη : IsCrosscutH η) {a b : ℝ}
    (ha : Tendsto η (𝓝[>] 0) (𝓝 (a : ℂ))) (hb : Tendsto η (𝓝[<] 1) (𝓝 (b : ℂ)))
    (ha0 : 0 < a) (hab : a < b) (N : ℝ) : FL3Arc (hullComp η) id (Ioo (-N) 0) where
  meas := measurableSet_Ioo
  chart x hx := by
    obtain ⟨r, hr, hsub, hfr⟩ := fl3a1_halfDisk hη ha hb ha0 hab hx.2.le
    exact ⟨r, hr, differentiableOn_id, fun z hz => hsub hz, fun z hz hzim => (hfr z hz hzim).2⟩
  inj x _ y _ h := Complex.ofReal_injective h

/-- Order bookkeeping: an interval `(c, d)` avoiding `[α, β]`, with end points outside
`[α, β]`, lies strictly on one side. -/
lemma fl3a1_side {α β c d : ℝ} (hαβ : α < β) (hc : c < α ∨ β < c)
    (hd : d < α ∨ β < d) (hI : ∀ t ∈ Ioo c d, t < α ∨ β < t) : d < α ∨ β < c := by
  rcases hd with h | h
  · exact Or.inl h
  rcases hc with h' | h'
  · rcases hI α ⟨h', by linarith⟩ with h'' | h'' <;> linarith
  · exact Or.inr h'

/-- **FL3-ASM1: the first symmetry step** (Field–Lawler, EJP 20 (2015), pp. 7 and 9, via
Lawler, *Conformally Invariant Processes in the Plane*, Prop. 5.8, p. 105). -/
theorem fl3_first_symm {η : ℝ → ℂ} (hη : IsCrosscutH η) {a b N : ℝ}
    (ha : Tendsto η (𝓝[>] 0) (𝓝 (a : ℂ))) (hb : Tendsto η (𝓝[<] 1) (𝓝 (b : ℂ)))
    (ha0 : 0 < a) (hab : a < b) (hN : 0 < N)
    {G h : ℂ → ℝ} (hG : IsHarmMeas (hullComp η) (((↑) : ℝ → ℂ) '' Ioo (-N) 0) G)
    (hh : IsHarmMeas (hullComp η) (arcH η) h)
    {ψ : ℂ → ℂ} {J : Set ℝ} (hψ : FL3Arc (hullComp η) ψ J)
    (hψJ : ψ '' (((↑) : ℝ → ℂ) '' J) = arcH η) :
    excR h (Ioo (-N) 0) = excR (G ∘ ψ) J := by
  obtain ⟨F, α, β, hF, hαβ, -, -, hIoo, hrest⟩ := fl3u_FL3Unif_pieces hη ha hb hab
  set g : ℝ → ℝ := fun x => (F (x : ℂ)).re with hg
  have hpt : ∀ x ∈ Icc (-N) 0, ((x : ℂ) ∈ frontier (hullComp η)) ∧ (x : ℂ) ∉ closure (arcH η) :=
    fun x hx => by
      obtain ⟨r, hr, -, hfr⟩ := fl3a1_halfDisk hη ha hb ha0 hab hx.2
      exact ⟨(hfr _ (mem_ball_self hr) (by simp)).2, (hfr _ (mem_ball_self hr) (by simp)).1⟩
  have havoid : ∀ x ∈ Icc (-N) 0, g x < α ∨ β < g x := fun x hx =>
    (hrest _ (hpt x hx).1 (hpt x hx).2).2.2
  have hcont : ContinuousOn g (Icc (-N) 0) :=
    Complex.continuous_re.comp_continuousOn (hF.cont.comp continuous_ofReal.continuousOn
      fun x hx => frontier_subset_closure (hpt x hx).1)
  have hreal : ∀ z ∈ frontier (hullComp η), F z = (((F z).re : ℝ) : ℂ) := fun z hz =>
    Complex.ext (by simp) (by simp [hF.bdry_real z hz])
  have hinj : InjOn g (Icc (-N) 0) := fun x hx y hy hxy => by
    have := hF.bdry_inj (hpt x hx).1 (hpt y hy).1
      (by rw [hreal _ (hpt x hx).1, hreal _ (hpt y hy).1]; exact congrArg _ hxy)
    exact Complex.ofReal_injective this
  have hN0 : -N ≤ 0 := by linarith
  have hsub : ∀ t ∈ g '' Ioo (-N) 0, t < α ∨ β < t := by
    rintro _ ⟨x, hx, rfl⟩
    exact havoid x (Ioo_subset_Icc_self hx)
  have hA := fl3a1_arc_id hη ha hb ha0 hab N
  have hIB : (fun x : ℝ => (F (ψ x)).re) '' J = Ioo α β := by
    rw [← hIoo, ← hψJ, image_image, image_image]
  have hωA : IsHarmMeas (hullComp η) (id '' (((↑) : ℝ → ℂ) '' Ioo (-N) 0)) G := by
    rwa [image_id]
  have hωB : IsHarmMeas (hullComp η) (ψ '' (((↑) : ℝ → ℂ) '' J)) h := by rwa [hψJ]
  have hlt : -N < 0 := by linarith
  have hIcc0 : (0 : ℝ) ∈ Icc (-N) 0 := ⟨hN0, le_rfl⟩
  have hIccN : (-N : ℝ) ∈ Icc (-N) 0 := ⟨le_rfl, hN0⟩
  rcases hcont.strictMonoOn_of_injOn_Icc' hN0 hinj with hmono | hmono
  · have hI := hcont.image_Ioo_of_strictMonoOn hN0 hmono
    have hcd : g (-N) < g 0 := hmono hIccN hIcc0 hlt
    have := fl3Sym_excR_symm' hF hA hψ hcd hαβ
      (fl3a1_side hαβ (havoid _ hIccN) (havoid _ hIcc0) (hI ▸ hsub)) hI hIB hωA hωB
    simpa using this
  · have hI := hcont.image_Ioo_of_strictAntiOn hN0 hmono
    have hcd : g 0 < g (-N) := hmono hIccN hIcc0 hlt
    have := fl3Sym_excR_symm' hF hA hψ hcd hαβ
      (fl3a1_side hαβ (havoid _ hIcc0) (havoid _ hIccN) (hI ▸ hsub)) hI hIB hωA hωB
    simpa using this

end FieldLawler
end QuantumZipper
