import QuantumZipper.Proofs.Thm18.ASep3Inner
import QuantumZipper.Proofs.Thm18.ASep3Glue

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP3 (step 15): one continuous modification of the dilated pushed-circle averages

The scale analogue of `RegUnif.exists_contMod_ν4`: with parameters
`q = (t, Re c, Im c, s, r) ∈ ℝ⁵`, clamped time `t ↦ max (min t T) 0`, centre `Re c + i |Im c|`,
scale `s > 0`, radius `r > 0`, the Gaussian family
`Z q = X((fc(c, r).map f_t⁻¹).map (s ·))` has a modification that is almost surely continuous on
`{s > 0, r > 0}` (**`exists_contMod_νT_rescale`**): on every small rational box, `genFam_νT`
composed with the (`1`-Lipschitz) clamp (`genFam_comp`), dilated (`genFam_dil`), and the
Kolmogorov step `GenUC.exists_contMod_gen`; then `ae_glue_modification`. Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace ASep

open GenUC

/-- **`GenFam` along a Lipschitz reparametrization.** -/
theorem genFam_comp {n m : ℕ} {S : Set (Fin n → ℝ)} {S' : Set (Fin m → ℝ)}
    {μ : (Fin m → ℝ) → ℝ → Measure ℂ} {M : ℝ≥0∞} {K c : ℝ} (hF : GenFam S' μ M K c)
    (f : (Fin n → ℝ) → Fin m → ℝ) (hfS : MapsTo f S S') {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ p p', dist (f p) (f p') ≤ L * dist p p') :
    ∃ K' : ℝ, GenFam S (fun p ρ => μ (f p) ρ) M K' c := by
  have hc := hF.c_pos
  refine ⟨K * (L + 1) ^ c, ⟨fun p hp ρ hρ => hF.adm _ (hfS hp) ρ hρ,
    fun p hp ρ hρ => hF.mass _ (hfS hp) ρ hρ, by have := hF.K_nonneg; positivity, hc,
    fun p hp p' hp' ρ hρ ρ' hρ' => ?_⟩⟩
  refine (hF.energy _ (hfS hp) _ (hfS hp') ρ hρ ρ' hρ').trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hF.K_nonneg
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  refine Real.rpow_le_rpow (by positivity) ?_ hc.le
  have h1 := hf p p'
  have h2 : 0 ≤ dist p p' := dist_nonneg
  have h3 : 0 ≤ |ρ - ρ'| := abs_nonneg _
  nlinarith

/-- The clamp of `(t, Re c, Im c)`. -/
def clampT (T : ℝ) (p : Fin 3 → ℝ) : Fin 3 → ℝ := ![max (min (p 0) T) 0, p 1, |p 2|]

theorem dist_clampT_le (T : ℝ) (p p' : Fin 3 → ℝ) : dist (clampT T p) (clampT T p') ≤ dist p p' := by
  refine (dist_pi_le_iff dist_nonneg).2 fun i => ?_
  rw [Real.dist_eq]
  have h0 := dist_le_pi_dist p p' 0
  have h1 := dist_le_pi_dist p p' 1
  have h2 := dist_le_pi_dist p p' 2
  rw [Real.dist_eq] at h0 h1 h2
  fin_cases i
  · exact (RegCont.abs_clamp_sub_le _ _ _).trans h0
  · exact h1
  · exact (abs_abs_sub_abs_le _ _).trans h2

theorem clampT_mem {T : ℝ} (hT : 0 ≤ T) (p : Fin 3 → ℝ) : clampT T p 0 ∈ Icc (0 : ℝ) T :=
  ⟨le_max_right _ _, max_le (min_le_right _ _) hT⟩

theorem norm_cpt_clampT_le (T : ℝ) (p : Fin 3 → ℝ) : ‖cpt (clampT T p)‖ ≤ |p 1| + |p 2| := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  show |p 1| + |(|p 2|)| ≤ _
  rw [abs_abs]

/-- The five-parameter dilated pushed-circle family. -/
def nu5 (W : ℝ → ℝ) (T : ℝ) (q : Fin 5 → ℝ) : Measure ℂ :=
  (RegCont.νT W (cpt (clampT T (Fin.init (Fin.init q)))) (q 4)
    (clampT T (Fin.init (Fin.init q)) 0)).map fun z => ((q 3 : ℝ) : ℂ) * z

/-- **One continuous modification of the dilated pushed-circle averages.** -/
theorem exists_contMod_νT_rescale {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) {T a CH : ℝ} (hT : 0 < T) (ha : 0 < a) (ha1 : a ≤ 1) (hCH : 0 ≤ CH)
    (hH : ∀ t ∈ Icc (0 : ℝ) T, ∀ t' ∈ Icc (0 : ℝ) T, |t - t'| ≤ 1 / 2 →
      |W t - W t'| ≤ CH * |t - t'| ^ a) :
    ∃ Y : (Fin 5 → ℝ) → Ω → ℝ,
      (∀ᵐ ω ∂P, ContinuousOn (fun q => Y q ω) {q | 0 < q 3 ∧ 0 < q 4}) ∧
      ∀ q ∈ {q : Fin 5 → ℝ | 0 < q 3 ∧ 0 < q 4},
        (fun ω => Y q ω) =ᵐ[P] fun ω => X ω (nu5 W T q) := by
  have hU : IsOpen {q : Fin 5 → ℝ | 0 < q 3 ∧ 0 < q 4} :=
    (isOpen_lt continuous_const (continuous_apply 3)).inter
      (isOpen_lt continuous_const (continuous_apply 4))
  refine ae_glue_modification hU fun lo hi hsub hsmall => ?_
  rcases (ratBox lo hi).eq_empty_or_nonempty with he | hne
  · exact ⟨fun _ _ => 0, fun ω => continuousOn_const, fun p hp => by
      rw [he] at hp; exact absurd hp (notMem_empty p)⟩
  obtain ⟨q₀, hq₀⟩ := hne
  have hlohi : ∀ i, (lo i : ℝ) ≤ hi i := fun i => (hq₀ i (mem_univ i)).1.trans (hq₀ i (mem_univ i)).2
  -- the box data
  set r₀ : ℝ := ((lo 4 : ℚ) : ℝ) with hr₀
  set s₀ : ℝ := ((lo 3 : ℚ) : ℝ) with hs₀
  have hbox4 : ∀ q ∈ ratBox lo hi, q 4 ∈ Icc r₀ (hi 4) := fun q hq => hq 4 (mem_univ _)
  have hbox3 : ∀ q ∈ ratBox lo hi, q 3 ∈ Icc s₀ (hi 3) := fun q hq => hq 3 (mem_univ _)
  have hlo4 : 0 < r₀ := by
    have hq := hsub (show (fun i => if i = 4 then (lo 4 : ℝ) else q₀ i) ∈ ratBox lo hi from
      fun i _ => by
        by_cases h : i = 4
        · subst h; simp only [if_pos rfl]; exact ⟨le_rfl, hlohi 4⟩
        · simp only [if_neg h]; exact hq₀ i (mem_univ i))
    have := hq.2
    simp only [if_pos rfl] at this
    exact this
  have hlo3 : 0 < s₀ := by
    have hq := hsub (show (fun i => if i = 3 then (lo 3 : ℝ) else q₀ i) ∈ ratBox lo hi from
      fun i _ => by
        by_cases h : i = 3
        · subst h; simp only [if_pos rfl]; exact ⟨le_rfl, hlohi 3⟩
        · simp only [if_neg h]; exact hq₀ i (mem_univ i))
    have := hq.1
    simp only [if_pos rfl] at this
    exact this
  set R : ℝ := |(lo 1 : ℝ)| + |(hi 1 : ℝ)| + |(lo 2 : ℝ)| + |(hi 2 : ℝ)| with hR
  have hR0 : 0 ≤ R := by positivity
  set S₃ : Set (Fin 3 → ℝ) := ratBox (Fin.init (Fin.init lo)) (Fin.init (Fin.init hi))
  set S' : Set (Fin 3 → ℝ) := {p | p 0 ∈ Icc (0 : ℝ) T ∧ ‖cpt p‖ ≤ 2 * R}
  have hbd : ∀ (x l h : ℝ), x ∈ Icc l h → |x| ≤ |l| + |h| := fun x l h hx => by
    rw [abs_le]; constructor <;> linarith [neg_abs_le l, le_abs_self h, hx.1, hx.2,
      abs_nonneg l, abs_nonneg h]
  have hmaps : MapsTo (clampT T) S₃ S' := fun p hp => by
    refine ⟨clampT_mem hT.le p, (norm_cpt_clampT_le T p).trans ?_⟩
    have h1 := hbd _ _ _ (hp 1 (mem_univ _))
    have h2 := hbd _ _ _ (hp 2 (mem_univ _))
    have e1 : ((Fin.init (Fin.init lo) 1 : ℚ) : ℝ) = lo 1 := rfl
    have e2 : ((Fin.init (Fin.init hi) 1 : ℚ) : ℝ) = hi 1 := rfl
    have e3 : ((Fin.init (Fin.init lo) 2 : ℚ) : ℝ) = lo 2 := rfl
    have e4 : ((Fin.init (Fin.init hi) 2 : ℚ) : ℝ) = hi 2 := rfl
    rw [e1, e2] at h1; rw [e3, e4] at h2
    linarith [abs_nonneg (lo 1 : ℝ), abs_nonneg (hi 2 : ℝ)]
  obtain ⟨K, c, hF'⟩ := genFam_νT hW hW0 ha ha1 hCH hH hlo4 (S := S') fun p hp => hp
  obtain ⟨K₁, hF₁⟩ := genFam_comp hF' (clampT T) hmaps zero_le_one
    (fun p p' => by rw [one_mul]; exact dist_clampT_le T p p')
  -- Frostman and support of the composed family
  obtain ⟨M, hM⟩ := RegCont.exists_abs_le_on_Icc hW T
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, hT.le⟩)
  set Rr : ℝ := 2 * R + r₀ + 1
  have hr : ∀ ρ ∈ Icc (0 : ℝ) 1, r₀ ≤ r₀ + ρ := fun ρ hρ => by linarith [hρ.1]
  have hwR : ∀ p ∈ S₃, ∀ ρ ∈ Icc (0 : ℝ) 1, ‖cpt (clampT T p)‖ + (r₀ + ρ) ≤ Rr :=
    fun p hp ρ hρ => by have := (hmaps hp).2; linarith [hρ.2]
  obtain ⟨C₀, hC₀⟩ := Metric.isBounded_iff.1 (isCompact_ratBox (Fin.init (Fin.init lo))
    (Fin.init (Fin.init hi))).isBounded
  obtain ⟨K₂, c₂, hFd⟩ := genFam_dil hF₁ hlo3 (s₁ := (hi 3 : ℝ)) (by norm_num : (0 : ℝ) < 1 / 3)
    (by norm_num) (RegUnif.frostC_nonneg (R := Rr) hT.le hlo4)
    (RegCont.revBound_nonneg (R₀ := Rr) (by linarith) hT.le) (le_max_right C₀ 0)
    (fun p hp ρ hρ => fun x y hy =>
      (RegUnif.νT_box_facts hW hW0 hlo4 hM (clampT_mem hT.le p) (hr ρ hρ) (hwR p hp ρ hρ)).2.1
        x y hy)
    (fun p hp ρ hρ => (RegUnif.νT_box_facts hW hW0 hlo4 hM (clampT_mem hT.le p) (hr ρ hρ)
      (hwR p hp ρ hρ)).2.2.mono fun z hz => hz.2)
    (fun p hp p' hp' => (hC₀ hp hp').trans (le_max_left _ _))
  have hF4 : GenFam (ratBox (Fin.init lo) (Fin.init hi))
      (dilFam fun p ρ => nuTFam W r₀ (clampT T p) ρ) 1 K₂ c₂ := by
    rw [ratBox_eq_dilSet]; exact hFd
  obtain ⟨Y4, hY4c, hY4e⟩ := exists_contMod_gen hX hF4
    (isLipRetr_ratBox fun i => hlohi i.castSucc)
  refine ⟨fun q ω => Y4 (Fin.init q) (q 4 - r₀) ω, fun ω => ?_, fun q hq => ?_⟩
  · have hc : Continuous fun q : Fin 5 → ℝ => (Fin.init q, q 4 - r₀) :=
      (continuous_pi fun i => continuous_apply _).prodMk ((continuous_apply 4).sub continuous_const)
    exact ((hY4c ω).comp hc).continuousOn
  · have hq4 : Fin.init q ∈ ratBox (Fin.init lo) (Fin.init hi) := fun i _ => hq i.castSucc (mem_univ _)
    have hρ : q 4 - r₀ ∈ Icc (0 : ℝ) 1 := by
      have h1 := hbox4 q hq
      have h2 := hsmall 4
      constructor <;> linarith [h1.1, h1.2]
    have e : dilFam (fun p ρ => nuTFam W r₀ (clampT T p) ρ) (Fin.init q) (q 4 - r₀) =
        nu5 W T q := by
      simp only [dilFam, nuTFam, nu5]
      rw [add_sub_cancel]
      rfl
    rw [← e]
    exact hY4e _ hq4 _ hρ

end ASep
end QuantumZipper
