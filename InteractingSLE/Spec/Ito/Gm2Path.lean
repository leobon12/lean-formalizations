import InteractingSLE.Spec.Ito.Gm2Engine
import InteractingSLE.Spec.Ito.Dynkin
import InteractingSLE.Spec.Ito.GenStieltjes

/-!
# Pathwise defects of the mixed Itô formula

Packet PROVE-ITO-GEN2. Deterministic estimates for one path: a finite-variation coordinate `y`
(`Δy = Σₖ ∫ cₖ dUₖ` against continuous Stieltjes integrators `Uₖ`), a continuous real coordinate `x`
and a bracket `A` (`ΔA = Σₖ ∫ αₖ dUₖ`, `αₖ ≥ 0`). For a `C³` function `F` with Lipschitz first and second
derivatives, the Itô defect of one cell `[a, b]`,

`F(y_b, x_b) − F(y_a, x_a) − Σₖ ∫_{(a,b]} (∂_y F(y, x) cₖ + ½ ∂²_x F(y, x) αₖ) dUₖ
  − ∂_x F(y_a, x_a) Δx − ½ ∂²_x F(y_a, x_a) (Δx² − ΔA)`,

is at most `C |Δx|³ + C η (3 TV + ΔA)` when the paths oscillate by at most `η` on the cell
(`abs_cellDefect_le`). No density of the integrators with respect to Lebesgue measure is used; the
finite-variation coordinates enter only through first-order Taylor expansions.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Finset
open scoped NNReal ENNReal

namespace InteractingSLE.Ito.Gm2

section Cell

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {m : ℕ} {F : E × ℝ → ℝ} {C : ℝ}

omit [CompleteSpace E] in
/-- **First-order Taylor bound in the finite-variation slot**:
`|F(e', x) − F(e, x) − ∂_y F(e, x)(e' − e)| ≤ C ‖e' − e‖²` for `C`-Lipschitz `DF`. -/
theorem abs_sub_partialFst_le (hF : ContDiff ℝ 3 F) (hC0 : 0 ≤ C)
    (hLip1 : ∀ p q, ‖fderiv ℝ F p - fderiv ℝ F q‖ ≤ C * ‖p - q‖) (e e' : E) (x : ℝ) :
    |F (e', x) - F (e, x) - partialFst F (e, x) (e' - e)| ≤ C * ‖e' - e‖ ^ 2 := by
  have hDF : ∀ p, HasFDerivAt F (fderiv ℝ F p) p := fun p =>
    ((hF.differentiable (by norm_num)) p).hasFDerivAt
  set g : E → ℝ := fun v => F (v, x) - partialFst F (e, x) v with hgdef
  have hg : ∀ v, HasFDerivAt g (partialFst F (v, x) - partialFst F (e, x)) v := fun v =>
    ((hDF (v, x)).comp v (hasFDerivAt_prodMk_left v x)).sub (partialFst F (e, x)).hasFDerivAt
  have hb : ∀ v ∈ Metric.closedBall e ‖e' - e‖,
      ‖partialFst F (v, x) - partialFst F (e, x)‖ ≤ C * ‖e' - e‖ := by
    intro v hv
    refine (norm_partialFst_sub_le _ _).trans ((hLip1 _ _).trans ?_)
    have hn : ‖((v, x) : E × ℝ) - (e, x)‖ = ‖v - e‖ := by
      rw [Prod.mk_sub_mk, sub_self, Prod.norm_def]; simp
    rw [hn]
    exact mul_le_mul_of_nonneg_left (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hv) hC0
  have h := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (f := g)
    (fun v _ => (hg v).hasFDerivWithinAt) hb (convex_closedBall e ‖e' - e‖)
    (Metric.mem_closedBall_self (norm_nonneg _) : e ∈ Metric.closedBall e ‖e' - e‖)
    (show e' ∈ Metric.closedBall e ‖e' - e‖ by
      simp only [Metric.mem_closedBall, dist_eq_norm, le_refl])
  have he : g e' - g e = F (e', x) - F (e, x) - partialFst F (e, x) (e' - e) := by
    simp only [hgdef, map_sub]; ring
  rw [he, Real.norm_eq_abs] at h
  calc _ ≤ C * ‖e' - e‖ * ‖e' - e‖ := h
    _ = C * ‖e' - e‖ ^ 2 := by ring

omit [CompleteSpace E] in
/-- **Second-order Taylor bound in the martingale slot** (QuantumZipper's `taylor2_bound` on the
vertical line): `|F(e, x') − F(e, x) − ∂_x F Δx − ½ ∂²_x F Δx²| ≤ C |Δx|³`. -/
theorem abs_taylor_snd_le (hF : ContDiff ℝ 3 F) (hC0 : 0 ≤ C)
    (hLip2 : ∀ p q, ‖iteratedFDeriv ℝ 2 F p - iteratedFDeriv ℝ 2 F q‖ ≤ C * ‖p - q‖)
    (e : E) (x x' : ℝ) :
    |F (e, x') - F (e, x) - partialSnd F (e, x) * (x' - x) -
      1 / 2 * partialSndSnd F (e, x) * (x' - x) ^ 2| ≤ C * |x' - x| ^ 3 := by
  have hTay := QuantumZipper.Dynkin.taylor2_bound hF hC0 hLip2 (e, x) ((0 : E), x' - x)
  have hw : ((e, x) + ((0 : E), x' - x) : E × ℝ) = (e, x') := by
    simp only [Prod.mk_add_mk, add_zero, add_sub_cancel]
  have hwn : ‖((0 : E), x' - x)‖ = |x' - x| := by simp [Prod.norm_def]
  have hlin : fderiv ℝ F (e, x) ((0 : E), x' - x) = partialSnd F (e, x) * (x' - x) := by
    have : ((0 : E), x' - x) = (x' - x) • ((0 : E), (1 : ℝ)) := by simp
    rw [this, map_smul, smul_eq_mul, partialSnd, mul_comm]
  have hquad : iteratedFDeriv ℝ 2 F (e, x) ![((0 : E), x' - x), ((0 : E), x' - x)] =
      partialSndSnd F (e, x) * (x' - x) ^ 2 := by
    rw [QuantumZipper.Dynkin.iteratedFDeriv_two_vec]
    have : ((0 : E), x' - x) = (x' - x) • ((0 : E), (1 : ℝ)) := by simp
    rw [this, map_smul, map_smul, smul_apply, smul_eq_mul, smul_eq_mul,
      partialSndSnd]
    ring
  rw [hw, hlin, hquad, hwn] at hTay
  calc _ = |F (e, x') - F (e, x) - partialSnd F (e, x) * (x' - x) -
        (1 / 2) * (partialSndSnd F (e, x) * (x' - x) ^ 2)| := by ring_nf
    _ ≤ C * |x' - x| ^ 3 := hTay

/-- A continuous integrand is integrable on a bounded cell for a Stieltjes measure. -/
lemma integrableOn_Ioc_of_continuous {G : Type*} [NormedAddCommGroup G] (U : StieltjesFunction ℝ≥0)
    {g : ℝ≥0 → G} (hg : Continuous g) (a b : ℝ≥0) : IntegrableOn g (Ioc a b) U.measure :=
  hg.integrableOn_Icc.mono_set Ioc_subset_Icc_self

/-- **The finite-variation term of one cell.** If `‖L − L_u‖ ≤ β` on `(a, b]`, then
`|L(Σₖ ∫ cₖ dUₖ) − Σₖ ∫ L_u(cₖ(u)) dUₖ(u)| ≤ β Σₖ ∫ ‖cₖ‖ dUₖ`. -/
theorem abs_clm_sum_integral_sub_le (U : Fin m → StieltjesFunction ℝ≥0) (L : E →L[ℝ] ℝ)
    {Lu : ℝ≥0 → E →L[ℝ] ℝ} (hLu : Continuous Lu) {cc : Fin m → ℝ≥0 → E}
    (hcc : ∀ k, Continuous (cc k)) {a b : ℝ≥0} {β : ℝ}
    (hβ : ∀ u ∈ Ioc a b, ‖L - Lu u‖ ≤ β) :
    |L (∑ k, ∫ u in Ioc a b, cc k u ∂(U k).measure) -
        ∑ k, ∫ u in Ioc a b, Lu u (cc k u) ∂(U k).measure| ≤
      β * ∑ k, ∫ u in Ioc a b, ‖cc k u‖ ∂(U k).measure := by
  have hi (k : Fin m) := integrableOn_Ioc_of_continuous (U k) (hcc k) a b
  have hiL (k : Fin m) : IntegrableOn (fun u => Lu u (cc k u)) (Ioc a b) (U k).measure :=
    integrableOn_Ioc_of_continuous (U k) (hLu.clm_apply (hcc k)) a b
  have hiL0 (k : Fin m) : IntegrableOn (fun u => L (cc k u)) (Ioc a b) (U k).measure :=
    integrableOn_Ioc_of_continuous (U k) (L.continuous.comp (hcc k)) a b
  have hin (k : Fin m) : IntegrableOn (fun u => ‖cc k u‖) (Ioc a b) (U k).measure :=
    integrableOn_Ioc_of_continuous (U k) (hcc k).norm a b
  rw [map_sum, ← sum_sub_distrib, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ => ?_)
  rw [← ContinuousLinearMap.integral_comp_comm L (hi k), ← integral_sub (hiL0 k) (hiL k),
    ← integral_const_mul, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le ((hin k).const_mul β)
    ((ae_restrict_iff' measurableSet_Ioc).2 (.of_forall fun u hu => ?_))
  rw [← sub_apply]
  exact ((L - Lu u).le_opNorm (cc k u)).trans
    (mul_le_mul_of_nonneg_right (hβ u hu) (norm_nonneg _))

/-- **The bracket term of one cell.** If `|c₀ − s_u| ≤ β` on `(a, b]` and `αₖ ≥ 0`, then
`|c₀ Σₖ ∫ αₖ dUₖ − Σₖ ∫ s_u αₖ(u) dUₖ(u)| ≤ β Σₖ ∫ αₖ dUₖ`. -/
theorem abs_const_mul_sum_integral_sub_le (U : Fin m → StieltjesFunction ℝ≥0) (c₀ : ℝ)
    {su : ℝ≥0 → ℝ} (hsu : Continuous su) {α : Fin m → ℝ≥0 → ℝ}
    (hα : ∀ k, Continuous (α k)) (hα0 : ∀ k u, 0 ≤ α k u) {a b : ℝ≥0} {β : ℝ}
    (hβ : ∀ u ∈ Ioc a b, |c₀ - su u| ≤ β) :
    |c₀ * (∑ k, ∫ u in Ioc a b, α k u ∂(U k).measure) -
        ∑ k, ∫ u in Ioc a b, su u * α k u ∂(U k).measure| ≤
      β * ∑ k, ∫ u in Ioc a b, α k u ∂(U k).measure := by
  have hi (k : Fin m) := integrableOn_Ioc_of_continuous (U k) (hα k) a b
  have his (k : Fin m) : IntegrableOn (fun u => su u * α k u) (Ioc a b) (U k).measure :=
    integrableOn_Ioc_of_continuous (U k) (hsu.mul (hα k)) a b
  rw [mul_sum, mul_sum, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ => ?_)
  rw [← integral_const_mul, ← integral_const_mul, ← integral_sub ((hi k).const_mul c₀) (his k),
    ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le ((hi k).const_mul β)
    ((ae_restrict_iff' measurableSet_Ioc).2 (.of_forall fun u hu => ?_))
  rw [← sub_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hα0 k u)]
  exact mul_le_mul_of_nonneg_right (hβ u hu) (hα0 k u)

/-- **The Itô defect of one cell.** Along a finite-variation `y` (`Δy = Σₖ ∫ cₖ dUₖ`), a continuous `x`
and a bracket increment `ΔA = Σₖ ∫ αₖ dUₖ` (`αₖ ≥ 0`), if both paths oscillate by at most `η` on
`[a, b]`, then the defect of `F` with frozen coefficients at `a` is at most
`C |Δx|³ + C η (3 Σₖ ∫ ‖cₖ‖ dUₖ + ΔA)`. -/
theorem abs_cellDefect_le (hF : ContDiff ℝ 3 F) (hC0 : 0 ≤ C)
    (hLip1 : ∀ p q, ‖fderiv ℝ F p - fderiv ℝ F q‖ ≤ C * ‖p - q‖)
    (hLip2' : ∀ p q, ‖fderiv ℝ (fderiv ℝ F) p - fderiv ℝ (fderiv ℝ F) q‖ ≤ C * ‖p - q‖)
    (hLip2 : ∀ p q, ‖iteratedFDeriv ℝ 2 F p - iteratedFDeriv ℝ 2 F q‖ ≤ C * ‖p - q‖)
    (U : Fin m → StieltjesFunction ℝ≥0) {y : ℝ≥0 → E} {x : ℝ≥0 → ℝ}
    {cc : Fin m → ℝ≥0 → E} {α : Fin m → ℝ≥0 → ℝ}
    (hyc : Continuous y) (hxc : Continuous x) (hcc : ∀ k, Continuous (cc k))
    (hαc : ∀ k, Continuous (α k)) (hα0 : ∀ k u, 0 ≤ α k u)
    {a b : ℝ≥0} (hab : a ≤ b) {Aa Ab : ℝ}
    (hy : y b - y a = ∑ k, ∫ u in Ioc a b, cc k u ∂(U k).measure)
    (hA : Ab - Aa = ∑ k, ∫ u in Ioc a b, α k u ∂(U k).measure)
    {η : ℝ} (hη : ∀ u ∈ Icc a b, ‖y u - y a‖ ≤ η ∧ |x u - x a| ≤ η) :
    |F (y b, x b) - F (y a, x a) -
        (∑ k, ∫ u in Ioc a b, (partialFst F (y u, x u) (cc k u) +
          1 / 2 * partialSndSnd F (y u, x u) * α k u) ∂(U k).measure)
      - partialSnd F (y a, x a) * (x b - x a)
      - 1 / 2 * partialSndSnd F (y a, x a) * ((x b - x a) ^ 2 - (Ab - Aa))|
    ≤ C * |x b - x a| ^ 3 +
        C * η * (3 * (∑ k, ∫ u in Ioc a b, ‖cc k u‖ ∂(U k).measure) + (Ab - Aa)) := by
  have hF1 : ContDiff ℝ 2 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have hDFc : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by norm_num)
  have hD2c : Continuous (fderiv ℝ (fderiv ℝ F)) := hF1.continuous_fderiv (by norm_num)
  have hPFc : Continuous (partialFst F) := hDFc.clm_comp continuous_const
  have hPSSc : Continuous (partialSndSnd F) :=
    (hD2c.clm_apply continuous_const).clm_apply continuous_const
  have hpath : Continuous fun u => ((y u, x u) : E × ℝ) := hyc.prodMk hxc
  have hη0 : 0 ≤ η := (norm_nonneg _).trans (hη a ⟨le_rfl, hab⟩).1
  -- the finite-variation increment
  have hΔy : ‖y b - y a‖ ≤ η := (hη b ⟨hab, le_rfl⟩).1
  have hΔyTV : ‖y b - y a‖ ≤ (∑ k, ∫ u in Ioc a b, ‖cc k u‖ ∂(U k).measure) := by
    rw [hy]
    refine (norm_sum_le _ _).trans (sum_le_sum fun k _ => ?_)
    exact norm_integral_le_integral_norm _
  have hTV0 : 0 ≤ (∑ k, ∫ u in Ioc a b, ‖cc k u‖ ∂(U k).measure) :=
    sum_nonneg fun k _ => setIntegral_nonneg measurableSet_Ioc
    fun u _ => norm_nonneg _
  have hΔA0 : 0 ≤ Ab - Aa := by
    rw [hA]; exact sum_nonneg fun k _ => setIntegral_nonneg measurableSet_Ioc fun u _ => hα0 k u
  -- the four pieces
  have hT1 := abs_sub_partialFst_le hF hC0 hLip1 (y a) (y b) (x b)
  have hT1' : C * ‖y b - y a‖ ^ 2 ≤ C * η * (∑ k, ∫ u in Ioc a b, ‖cc k u‖ ∂(U k).measure) := by
    calc C * ‖y b - y a‖ ^ 2 = C * ‖y b - y a‖ * ‖y b - y a‖ := by ring
      _ ≤ C * η * (∑ k, ∫ u in Ioc a b, ‖cc k u‖ ∂(U k).measure) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hΔy hC0) hΔyTV (norm_nonneg _)
          (mul_nonneg hC0 hη0)
  have hT2 := abs_taylor_snd_le hF hC0 hLip2 (y a) (x a) (x b)
  have hT3 := abs_clm_sum_integral_sub_le U (partialFst F (y a, x b))
    (Lu := fun u => partialFst F (y u, x u))
    (hPFc.comp hpath) hcc (a := a) (b := b) (β := C * (2 * η)) fun u hu => by
      have hu' : u ∈ Icc a b := Ioc_subset_Icc_self hu
      refine (norm_partialFst_sub_le _ _).trans ((hLip1 _ _).trans
        (mul_le_mul_of_nonneg_left ?_ hC0))
      rw [Prod.mk_sub_mk, Prod.norm_def, max_le_iff, Real.norm_eq_abs]
      constructor
      · rw [norm_sub_rev]; linarith [(hη u hu').1]
      · have h1 := (hη u hu').2
        have h2 := (hη b ⟨hab, le_rfl⟩).2
        calc |x b - x u| = |(x b - x a) - (x u - x a)| := by ring_nf
          _ ≤ |x b - x a| + |x u - x a| := abs_sub _ _
          _ ≤ 2 * η := by linarith
  have hT4 := abs_const_mul_sum_integral_sub_le U (partialSndSnd F (y a, x a))
    (su := fun u => partialSndSnd F (y u, x u)) (hPSSc.comp hpath) hαc hα0 (a := a) (b := b)
    (β := C * η) fun u hu => by
      have hu' : u ∈ Icc a b := Ioc_subset_Icc_self hu
      refine (abs_partialSndSnd_sub_le _ _).trans ((hLip2' _ _).trans
        (mul_le_mul_of_nonneg_left ?_ hC0))
      rw [Prod.mk_sub_mk, Prod.norm_def, max_le_iff, Real.norm_eq_abs]
      exact ⟨by rw [norm_sub_rev]; exact (hη u hu').1, by rw [abs_sub_comm]; exact (hη u hu').2⟩
  -- the drift integral splits
  have hsplit : (∑ k, ∫ u in Ioc a b, (partialFst F (y u, x u) (cc k u) +
        1 / 2 * partialSndSnd F (y u, x u) * α k u) ∂(U k).measure) =
      (∑ k, ∫ u in Ioc a b, partialFst F (y u, x u) (cc k u) ∂(U k).measure) +
        1 / 2 * ∑ k, ∫ u in Ioc a b, partialSndSnd F (y u, x u) * α k u ∂(U k).measure := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun k _ => ?_
    have hi1 : IntegrableOn (fun u => partialFst F (y u, x u) (cc k u)) (Ioc a b) (U k).measure :=
      integrableOn_Ioc_of_continuous (U k) ((hPFc.comp hpath).clm_apply (hcc k)) a b
    have hi2 : IntegrableOn (fun u => 1 / 2 * (partialSndSnd F (y u, x u) * α k u)) (Ioc a b)
        (U k).measure :=
      (integrableOn_Ioc_of_continuous (U k) ((hPSSc.comp hpath).mul (hαc k)) a b).const_mul _
    rw [← integral_const_mul, ← integral_add hi1 hi2]
    exact setIntegral_congr_fun measurableSet_Ioc fun u _ => by ring
  have hkey : F (y b, x b) - F (y a, x a) -
        (∑ k, ∫ u in Ioc a b, (partialFst F (y u, x u) (cc k u) +
          1 / 2 * partialSndSnd F (y u, x u) * α k u) ∂(U k).measure)
      - partialSnd F (y a, x a) * (x b - x a)
      - 1 / 2 * partialSndSnd F (y a, x a) * ((x b - x a) ^ 2 - (Ab - Aa)) =
      (F (y b, x b) - F (y a, x b) - partialFst F (y a, x b) (y b - y a)) +
      (F (y a, x b) - F (y a, x a) - partialSnd F (y a, x a) * (x b - x a) -
        1 / 2 * partialSndSnd F (y a, x a) * (x b - x a) ^ 2) +
      (partialFst F (y a, x b) (∑ k, ∫ u in Ioc a b, cc k u ∂(U k).measure) -
        ∑ k, ∫ u in Ioc a b, partialFst F (y u, x u) (cc k u) ∂(U k).measure) +
      1 / 2 * (partialSndSnd F (y a, x a) * (Ab - Aa) -
        ∑ k, ∫ u in Ioc a b, partialSndSnd F (y u, x u) * α k u ∂(U k).measure) := by
    rw [hsplit, ← hy]; ring
  rw [hkey]
  calc _ ≤ |F (y b, x b) - F (y a, x b) - partialFst F (y a, x b) (y b - y a)| +
        |F (y a, x b) - F (y a, x a) - partialSnd F (y a, x a) * (x b - x a) -
          1 / 2 * partialSndSnd F (y a, x a) * (x b - x a) ^ 2| +
        |partialFst F (y a, x b) (∑ k, ∫ u in Ioc a b, cc k u ∂(U k).measure) -
          ∑ k, ∫ u in Ioc a b, partialFst F (y u, x u) (cc k u) ∂(U k).measure| +
        1 / 2 * |partialSndSnd F (y a, x a) * (Ab - Aa) -
          ∑ k, ∫ u in Ioc a b, partialSndSnd F (y u, x u) * α k u ∂(U k).measure| := by
        refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
          (add_le_add (abs_add_le _ _) le_rfl)) ?_)
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    _ ≤ C * η * (∑ k, ∫ u in Ioc a b, ‖cc k u‖ ∂(U k).measure) + C * |x b - x a| ^ 3 +
        C * (2 * η) * (∑ k, ∫ u in Ioc a b, ‖cc k u‖ ∂(U k).measure) +
        1 / 2 * (C * η * (Ab - Aa)) := by
        rw [← hA] at hT4
        linarith [hT1.trans hT1', hT2, hT3, hT4]
    _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hC0 hη0) hΔA0]

end Cell

/-- Additivity of a Stieltjes integral of a continuous integrand: `∫_{(0,b]} − ∫_{(0,a]} = ∫_{(a,b]}`. -/
lemma integral_Ioc_zero_sub {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (U : StieltjesFunction ℝ≥0) {g : ℝ≥0 → G} (hg : Continuous g) {a b : ℝ≥0} (hab : a ≤ b) :
    (∫ u in Ioc 0 b, g u ∂U.measure) - (∫ u in Ioc 0 a, g u ∂U.measure) =
      ∫ u in Ioc a b, g u ∂U.measure := by
  have hd : Disjoint (Ioc (0 : ℝ≥0) a) (Ioc a b) :=
    Set.disjoint_left.2 fun _ hu hv => (not_lt_of_ge hu.2) hv.1
  have h := setIntegral_union hd measurableSet_Ioc (integrableOn_Ioc_of_continuous U hg 0 a)
    (integrableOn_Ioc_of_continuous U hg a b)
  rw [Ioc_union_Ioc_eq_Ioc (show (0 : ℝ≥0) ≤ a from bot_le) hab] at h
  rw [h, add_sub_cancel_left]

/-! ### Oscillation on the uniform grids -/

/-- **Uniform smallness of the cell oscillations**: for a continuous path and `η > 0`, eventually every
cell of the `n`-th uniform grid of `[s, t]` has oscillation at most `η` from its left end. -/
theorem eventually_cell_osc_le {G : Type*} [SeminormedAddCommGroup G] {y : ℝ≥0 → G}
    (hy : Continuous y) {s t : ℝ≥0} (hst : s ≤ t) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n in atTop, ∀ k < n, ∀ u ∈ Icc (MathFin.unifPartIcc s t n k)
      (MathFin.unifPartIcc s t n (k + 1)), ‖y u - y (MathFin.unifPartIcc s t n k)‖ ≤ η := by
  obtain ⟨δ, hδ, hosc⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_Icc (a := s) (b := t)).uniformContinuousOn_of_continuous hy.continuousOn) η hη
  obtain ⟨N, hN⟩ := exists_nat_gt (((t : ℝ) - s) / δ)
  have hts : (0 : ℝ) ≤ (t : ℝ) - s := sub_nonneg.2 (NNReal.coe_le_coe.2 hst)
  refine eventually_atTop.2 ⟨N + 1, fun n hn k hk u hu => ?_⟩
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  set g := MathFin.unifPartIcc s t n
  have hgm : Monotone g := MathFin.unifPartIcc_mono s t n
  have hgs : s ≤ g k := le_unifPartIcc s t n k
  have hgn : g n = t := MathFin.unifPartIcc_self hst hn0.ne'
  have hgt : g (k + 1) ≤ t := hgn ▸ hgm (show k + 1 ≤ n by omega)
  have hmesh : ((g (k + 1) : ℝ) - g k) < δ := by
    rw [MathFin.unifPartIcc_succ_sub hst]
    have hNn : ((t : ℝ) - s) / δ < n := hN.trans (by exact_mod_cast (show N < n by omega))
    rw [div_lt_iff₀ hδ] at hNn
    rw [div_lt_iff₀ hnR]; linarith
  have hu1 : u ∈ Icc s t := ⟨hgs.trans hu.1, hu.2.trans hgt⟩
  have hu2 : g k ∈ Icc s t := ⟨hgs, (hgm (Nat.le_succ k)).trans hgt⟩
  have hd : dist u (g k) < δ := by
    rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 hu.1))]
    have : (u : ℝ) ≤ g (k + 1) := NNReal.coe_le_coe.2 hu.2
    linarith
  have := hosc u hu1 (g k) hu2 hd
  rw [dist_eq_norm] at this
  exact this.le

/-! ### The mixed residual of a process -/

section Residual

variable {Ω : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}

/-- The drift density of the mixed Itô formula against the integrator `Uₖ`:
`∂_y F(Y_u, M_u) cₖ(u) + ½ ∂²_x F(Y_u, M_u) αₖ(u)`. -/
def driftDensity (F : E × ℝ → ℝ) (Y : ℝ≥0 → Ω → E) (M : ℝ≥0 → Ω → ℝ)
    (c : Fin m → ℝ≥0 → Ω → E) (a : Fin m → ℝ≥0 → Ω → ℝ) (k : Fin m) (u : ℝ≥0) (ω : Ω) : ℝ :=
  partialFst F (Y u ω, M u ω) (c k u ω) + 1 / 2 * partialSndSnd F (Y u ω, M u ω) * a k u ω

/-- **The mixed Itô residual** `F(Y_t, M_t) − F(Y_0, M_0) − Σₖ ∫_{(0,t]} driftDensityₖ dUₖ`, for a
finite-variation coordinate `Y = Y_0 + Σₖ ∫ cₖ dUₖ`, a martingale coordinate `M` and a bracket
`A = A_0 + Σₖ ∫ aₖ dUₖ`. -/
def residual (F : E × ℝ → ℝ) (Y : ℝ≥0 → Ω → E) (M : ℝ≥0 → Ω → ℝ)
    (U : Fin m → Ω → StieltjesFunction ℝ≥0) (c : Fin m → ℝ≥0 → Ω → E) (a : Fin m → ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  F (Y t ω, M t ω) - F (Y 0 ω, M 0 ω) -
    ∑ k, ∫ u in Ioc 0 t, driftDensity F Y M c a k u ω ∂(U k ω).measure

/-- **The bracket of the residual**: `Σₖ ∫_{(0,t]} (∂_x F(Y_u, M_u))² aₖ(u) dUₖ(u)`. -/
def bracket (F : E × ℝ → ℝ) (Y : ℝ≥0 → Ω → E) (M : ℝ≥0 → Ω → ℝ)
    (U : Fin m → Ω → StieltjesFunction ℝ≥0) (a : Fin m → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ k, ∫ u in Ioc 0 t, partialSnd F (Y u ω, M u ω) ^ 2 * a k u ω ∂(U k ω).measure

variable [CompleteSpace E] {F : E × ℝ → ℝ} {C : ℝ}
  {Y : ℝ≥0 → Ω → E} {M A : ℝ≥0 → Ω → ℝ} {U : Fin m → Ω → StieltjesFunction ℝ≥0}
  {c : Fin m → ℝ≥0 → Ω → E} {a : Fin m → ℝ≥0 → Ω → ℝ}

/-- **The excess of the residual's Itô defects along one grid**: if on every cell of the `n`-th grid of
`[s, t]` both paths oscillate by at most `η`, the excess is at most
`C η (3 Σₖ ∫_{(s,t]} ‖cₖ‖ dUₖ + A_t − A_s)`. -/
theorem defectExcess_residual_le (hF : ContDiff ℝ 3 F) (hC0 : 0 ≤ C)
    (hLip1 : ∀ p q, ‖fderiv ℝ F p - fderiv ℝ F q‖ ≤ C * ‖p - q‖)
    (hLip2' : ∀ p q, ‖fderiv ℝ (fderiv ℝ F) p - fderiv ℝ (fderiv ℝ F) q‖ ≤ C * ‖p - q‖)
    (hLip2 : ∀ p q, ‖iteratedFDeriv ℝ 2 F p - iteratedFDeriv ℝ 2 F q‖ ≤ C * ‖p - q‖)
    {ω : Ω} (hYc : Continuous (Y · ω)) (hMc : Continuous (M · ω))
    (hcc : ∀ k, Continuous (c k · ω)) (hac : ∀ k, Continuous (a k · ω))
    (ha0 : ∀ k u, 0 ≤ a k u ω)
    (hY : ∀ t, Y t ω = Y 0 ω + ∑ k, ∫ u in Ioc 0 t, c k u ω ∂(U k ω).measure)
    (hA : ∀ t, A t ω = A 0 ω + ∑ k, ∫ u in Ioc 0 t, a k u ω ∂(U k ω).measure)
    {s t : ℝ≥0} (hst : s ≤ t) (n : ℕ) {η : ℝ} (hη0 : 0 ≤ η)
    (hη : ∀ k < n, ∀ u ∈ Icc (MathFin.unifPartIcc s t n k) (MathFin.unifPartIcc s t n (k + 1)),
      ‖Y u ω - Y (MathFin.unifPartIcc s t n k) ω‖ ≤ η ∧
        |M u ω - M (MathFin.unifPartIcc s t n k) ω| ≤ η) :
    defectExcess (residual F Y M U c a) (fun r ω => partialSnd F (Y r ω, M r ω))
        (fun r ω => partialSndSnd F (Y r ω, M r ω)) M A C s t n ω ≤
      C * η * (3 * (∑ k, ∫ u in Ioc s t, ‖c k u ω‖ ∂(U k ω).measure) + (A t ω - A s ω)) := by
  set g := MathFin.unifPartIcc s t n with hg
  have hgm : Monotone g := MathFin.unifPartIcc_mono s t n
  have hF1 : ContDiff ℝ 2 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have hPFc : Continuous (partialFst F) := (hF.continuous_fderiv (by norm_num)).clm_comp
    continuous_const
  have hPSSc : Continuous (partialSndSnd F) :=
    ((hF1.continuous_fderiv (by norm_num)).clm_apply continuous_const).clm_apply continuous_const
  have hpath : Continuous fun u => ((Y u ω, M u ω) : E × ℝ) := hYc.prodMk hMc
  have hdc (k : Fin m) : Continuous fun u => driftDensity F Y M c a k u ω :=
    ((hPFc.comp hpath).clm_apply (hcc k)).add
      ((continuous_const.mul (hPSSc.comp hpath)).mul (hac k))
  -- the cell representations
  have hYcell (k : ℕ) : Y (g (k + 1)) ω - Y (g k) ω =
      ∑ j, ∫ u in Ioc (g k) (g (k + 1)), c j u ω ∂(U j ω).measure := by
    rw [hY (g (k + 1)), hY (g k), add_sub_add_left_eq_sub, ← sum_sub_distrib]
    exact sum_congr rfl fun j _ => integral_Ioc_zero_sub (U j ω) (hcc j) (hgm (Nat.le_succ k))
  have hAcell (k : ℕ) : A (g (k + 1)) ω - A (g k) ω =
      ∑ j, ∫ u in Ioc (g k) (g (k + 1)), a j u ω ∂(U j ω).measure := by
    rw [hA (g (k + 1)), hA (g k), add_sub_add_left_eq_sub, ← sum_sub_distrib]
    exact sum_congr rfl fun j _ => integral_Ioc_zero_sub (U j ω) (hac j) (hgm (Nat.le_succ k))
  have hXcell (k : ℕ) : residual F Y M U c a (g (k + 1)) ω - residual F Y M U c a (g k) ω =
      F (Y (g (k + 1)) ω, M (g (k + 1)) ω) - F (Y (g k) ω, M (g k) ω) -
        ∑ j, ∫ u in Ioc (g k) (g (k + 1)), driftDensity F Y M c a j u ω ∂(U j ω).measure := by
    have h : (∑ j, ∫ u in Ioc 0 (g (k + 1)), driftDensity F Y M c a j u ω ∂(U j ω).measure) -
        (∑ j, ∫ u in Ioc 0 (g k), driftDensity F Y M c a j u ω ∂(U j ω).measure) =
        ∑ j, ∫ u in Ioc (g k) (g (k + 1)), driftDensity F Y M c a j u ω ∂(U j ω).measure := by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun j _ => integral_Ioc_zero_sub (U j ω) (hdc j) (hgm (Nat.le_succ k))
    simp only [residual]
    linarith [h]
  -- each cell
  have hcell (k : ℕ) (hk : k ∈ range n) :
      max (|itoDefect (residual F Y M U c a) (fun r ω => partialSnd F (Y r ω, M r ω))
          (fun r ω => partialSndSnd F (Y r ω, M r ω)) M A (g k) (g (k + 1)) ω| -
        C * |M (g (k + 1)) ω - M (g k) ω| ^ 3) 0 ≤
      C * η * (3 * (∑ j, ∫ u in Ioc (g k) (g (k + 1)), ‖c j u ω‖ ∂(U j ω).measure) +
        (A (g (k + 1)) ω - A (g k) ω)) := by
    have hd := abs_cellDefect_le hF hC0 hLip1 hLip2' hLip2 (fun j => U j ω) hYc hMc hcc hac
      (fun j u => ha0 j u) (hgm (Nat.le_succ k)) (hYcell k) (hAcell k)
      (hη k (Finset.mem_range.1 hk))
    have hTV0 : 0 ≤ ∑ j, ∫ u in Ioc (g k) (g (k + 1)), ‖c j u ω‖ ∂(U j ω).measure :=
      sum_nonneg fun j _ => setIntegral_nonneg measurableSet_Ioc fun u _ => norm_nonneg _
    have hΔA0 : 0 ≤ A (g (k + 1)) ω - A (g k) ω := by
      rw [hAcell k]
      exact sum_nonneg fun j _ => setIntegral_nonneg measurableSet_Ioc fun u _ => ha0 j u
    refine max_le ?_ (by positivity)
    have he : itoDefect (residual F Y M U c a) (fun r ω => partialSnd F (Y r ω, M r ω))
        (fun r ω => partialSndSnd F (Y r ω, M r ω)) M A (g k) (g (k + 1)) ω =
        F (Y (g (k + 1)) ω, M (g (k + 1)) ω) - F (Y (g k) ω, M (g k) ω) -
          (∑ j, ∫ u in Ioc (g k) (g (k + 1)), (partialFst F (Y u ω, M u ω) (c j u ω) +
            1 / 2 * partialSndSnd F (Y u ω, M u ω) * a j u ω) ∂(U j ω).measure)
        - partialSnd F (Y (g k) ω, M (g k) ω) * (M (g (k + 1)) ω - M (g k) ω)
        - 1 / 2 * partialSndSnd F (Y (g k) ω, M (g k) ω) *
          ((M (g (k + 1)) ω - M (g k) ω) ^ 2 - (A (g (k + 1)) ω - A (g k) ω)) := by
      rw [itoDefect, hXcell k]; rfl
    rw [he]; linarith [hd]
  -- sum over the cells
  have hTV0 : 0 ≤ ∑ j, ∫ u in Ioc s t, ‖c j u ω‖ ∂(U j ω).measure :=
    sum_nonneg fun j _ => setIntegral_nonneg measurableSet_Ioc fun u _ => norm_nonneg _
  have hΔA0 : 0 ≤ A t ω - A s ω := by
    rw [hA t, hA s, add_sub_add_left_eq_sub, ← sum_sub_distrib]
    exact sum_nonneg fun j _ => by
      rw [integral_Ioc_zero_sub (U j ω) (hac j) hst]
      exact setIntegral_nonneg measurableSet_Ioc fun u _ => ha0 j u
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [defectExcess, range_zero, sum_empty]
    positivity
  have hg0 : g 0 = s := MathFin.unifPartIcc_zero s t n
  have hgn : g n = t := MathFin.unifPartIcc_self hst hn.ne'
  have hTVsum : (∑ k ∈ range n, ∑ j, ∫ u in Ioc (g k) (g (k + 1)), ‖c j u ω‖ ∂(U j ω).measure) =
      ∑ j, ∫ u in Ioc s t, ‖c j u ω‖ ∂(U j ω).measure := by
    rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [← hg0, ← hgn]
    exact (Gen.integral_Ioc_partition (U j ω).measure hgm n
      (integrableOn_Ioc_of_continuous (U j ω) (hcc j).norm _ _)).symm
  have hAsum : (∑ k ∈ range n, (A (g (k + 1)) ω - A (g k) ω)) = A t ω - A s ω := by
    rw [sum_range_sub (fun k => A (g k) ω) n]
    simp only [hg0, hgn]
  calc defectExcess (residual F Y M U c a) (fun r ω => partialSnd F (Y r ω, M r ω))
        (fun r ω => partialSndSnd F (Y r ω, M r ω)) M A C s t n ω
      ≤ ∑ k ∈ range n, C * η * (3 * (∑ j, ∫ u in Ioc (g k) (g (k + 1)), ‖c j u ω‖ ∂(U j ω).measure) +
          (A (g (k + 1)) ω - A (g k) ω)) := sum_le_sum hcell
    _ = C * η * (3 * (∑ k ∈ range n, ∑ j, ∫ u in Ioc (g k) (g (k + 1)), ‖c j u ω‖ ∂(U j ω).measure) +
          ∑ k ∈ range n, (A (g (k + 1)) ω - A (g k) ω)) := by
        rw [← mul_sum, sum_add_distrib, ← mul_sum]
    _ = _ := by rw [hTVsum, hAsum]

/-- **The excesses of the residual vanish along every path.** -/
theorem tendsto_defectExcess_residual (hF : ContDiff ℝ 3 F) (hC0 : 0 ≤ C)
    (hLip1 : ∀ p q, ‖fderiv ℝ F p - fderiv ℝ F q‖ ≤ C * ‖p - q‖)
    (hLip2' : ∀ p q, ‖fderiv ℝ (fderiv ℝ F) p - fderiv ℝ (fderiv ℝ F) q‖ ≤ C * ‖p - q‖)
    (hLip2 : ∀ p q, ‖iteratedFDeriv ℝ 2 F p - iteratedFDeriv ℝ 2 F q‖ ≤ C * ‖p - q‖)
    {ω : Ω} (hYc : Continuous (Y · ω)) (hMc : Continuous (M · ω))
    (hcc : ∀ k, Continuous (c k · ω)) (hac : ∀ k, Continuous (a k · ω))
    (ha0 : ∀ k u, 0 ≤ a k u ω)
    (hY : ∀ t, Y t ω = Y 0 ω + ∑ k, ∫ u in Ioc 0 t, c k u ω ∂(U k ω).measure)
    (hA : ∀ t, A t ω = A 0 ω + ∑ k, ∫ u in Ioc 0 t, a k u ω ∂(U k ω).measure)
    {s t : ℝ≥0} (hst : s ≤ t) :
    Tendsto (fun n => defectExcess (residual F Y M U c a) (fun r ω => partialSnd F (Y r ω, M r ω))
        (fun r ω => partialSndSnd F (Y r ω, M r ω)) M A C s t n ω) atTop (𝓝 0) := by
  set Q := 3 * (∑ k, ∫ u in Ioc s t, ‖c k u ω‖ ∂(U k ω).measure) + (A t ω - A s ω) with hQ
  have hTV0 : 0 ≤ ∑ j, ∫ u in Ioc s t, ‖c j u ω‖ ∂(U j ω).measure :=
    sum_nonneg fun j _ => setIntegral_nonneg measurableSet_Ioc fun u _ => norm_nonneg _
  have hΔA0 : 0 ≤ A t ω - A s ω := by
    rw [hA t, hA s, add_sub_add_left_eq_sub, ← sum_sub_distrib]
    exact sum_nonneg fun j _ => by
      rw [integral_Ioc_zero_sub (U j ω) (hac j) hst]
      exact setIntegral_nonneg measurableSet_Ioc fun u _ => ha0 j u
  have hQ0 : 0 ≤ Q := by positivity
  refine tendsto_order.2 ⟨fun b hb => .of_forall fun n => hb.trans_le
    (defectExcess_nonneg _ _ _ _ _ _ _ _ _ _), fun ε hε => ?_⟩
  set η := ε / (2 * (C * Q + 1)) with hηdef
  have hCQ : 0 ≤ C * Q := mul_nonneg hC0 hQ0
  have hη : 0 < η := div_pos hε (by positivity)
  filter_upwards [(eventually_cell_osc_le hYc hst hη).and (eventually_cell_osc_le hMc hst hη)]
    with n hn
  refine (defectExcess_residual_le hF hC0 hLip1 hLip2' hLip2 hYc hMc hcc hac ha0 hY hA hst n
    hη.le fun k hk u hu => ⟨hn.1 k hk u hu, by
      simpa only [Real.norm_eq_abs] using hn.2 k hk u hu⟩).trans_lt ?_
  rw [← hQ, mul_assoc, mul_comm η, ← mul_assoc, hηdef]
  rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
  nlinarith

end Residual

end InteractingSLE.Ito.Gm2
