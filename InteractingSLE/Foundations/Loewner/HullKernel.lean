import InteractingSLE.Foundations.Loewner.Hull
import InteractingSLE.Foundations.Loewner.Capacity
import InteractingSLE.Foundations.Loewner.CapacityEstimates
import InteractingSLE.Foundations.Complex.Kernel

/-!
# The kernel theorem for compact `ℍ`-hulls with the hydrodynamic normalization

Packet PROVE-GEO-HKERNEL. The half-plane form of Carathéodory's kernel theorem used by the
specification on p. 205 (`source/spec/p193-240.md`, proof of Aux. 45: "Kernel convergence gives
convergence of the hydrodynamically normalized maps `g_{K_N}` to `g_K` in the common interior"),
p. 357 (`p337-384.md`, Aux. 108: "The Loewner ODE gives kernel convergence") and p. 489
(`p433-480.md`: "Kernel convergence … give convergence of maps and derivatives"). References:
Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), §1.4; G. F. Lawler, *Conformally
invariant processes in the plane* (2005), §3.4, §4.7.

Kernel convergence is QuantumZipper's `KernelConvergesTo` (Pommerenke 1992, §1.4 (i)–(ii)),
applied to the domains `ℍ \ A n` and `ℍ \ B`; `g n`, `g` are the mapping-out functions
(`IsMapOut`, hydrodynamic normalization `g z − z → 0` at `∞`).

## Main results

* `tendstoLocallyUniformlyOn_of_kernelConvergesTo_H`: if `ℍ \ A n → ℍ \ B` in the kernel sense and
  the hulls `A n` lie in a common disc, then `g_{A n} → g_B` locally uniformly on `ℍ \ B`;
  `tendstoLocallyUniformlyOn_deriv_of_kernelConvergesTo_H`: so do the derivatives;
* `tendsto_hcap_of_kernelConvergesTo_H`: the half-plane capacities converge;
* `tendstoLocallyUniformlyOn_invFunOn_of_kernelConvergesTo_H`: the inverse maps `ℍ → ℍ \ A n`
  converge locally uniformly on `ℍ`;
* `kernelConvergesTo_H_of_tendstoLocallyUniformlyOn_invFunOn` (no boundedness needed) and
  `kernelConvergesTo_H_of_tendstoLocallyUniformlyOn`: the converse directions;
* `kernelConvergesTo_H_iff_tendstoLocallyUniformlyOn_invFunOn`,
  `kernelConvergesTo_H_iff_tendstoLocallyUniformlyOn`: the kernel theorem for hulls, both
  directions;
* `tendstoLocallyUniformlyOn_extension_of_kernelConvergesTo_H`: on a disc `B(y, s)`, `y ∈ ℝ`,
  avoiding all the hulls, holomorphic extensions of `g_{A n}` (Schwarz reflection) converge to that
  of `g_B`, with their derivatives (p. 205: "Reflection across a slightly larger untouched interval
  gives locally uniform convergence there as well, and hence convergence of the derivatives");
  `exists_norm_le_of_kernelConvergesTo_H`: the uniform growth bound behind it;
* `kernelConvergesTo_H_of_monotone`, `kernelConvergesTo_H_of_antitone`: increasing hulls (p. 205:
  "the domains `ℍ \ K_N` decrease in the kernel sense to `ℍ \ K`") and decreasing hulls (p. 489:
  approximation from outside); `tendstoLocallyUniformlyOn_of_monotone_H`,
  `tendstoLocallyUniformlyOn_of_antitone_H`: the maps converge in both cases;
* general tools: `tendstoUniformlyOn_dslope` (difference quotients of uniformly convergent
  holomorphic functions converge uniformly, by the maximum modulus principle) and
  `tendstoLocallyUniformlyOn_invFunOn` (inverses of locally uniformly convergent conformal maps
  converge, by Hurwitz's theorem).

## Proof

Fix `R` with all hulls in `B(0, R)`. The doubling of
`InteractingSLE.Foundations.Loewner.HullExists` (`dblΩ A R`, the image of
`ℂ̂ \ (A ∪ conj A ∪ [−2R, 2R])` under `z ↦ 1/(2R − z)`) turns the hull complements into simply
connected domains containing `0`, and the kernel convergence of `ℍ \ A n` into that of
`dblΩ (A n) R` with respect to `0` (`kernelConvergesTo_dblΩ`). The kernel convergence theorem for
the disc gives the convergence of the inverse normalized Riemann maps, and QuantumZipper's
`tendstoUniformlyOn_of_invFunOn` that of the symmetric Riemann maps `F n → F`. The mapping-out
function is the explicit `mapOut R F = 2F'(0) · J ∘ F ∘ ι − (P(0) − 2R)` (`isMapOut_mapOut`),
whose coefficients `F'(0)` and `P(0) = κ₂(0)/κ(0)` (`κ = dslope F 0`, `κ₂ = dslope κ 0`) converge
by `tendstoUniformlyOn_dslope`; the capacity is `−Re r'(0)` for the remainder `r`, which
converges likewise. The converse uses the disc theorem's `⇒` direction (no normalization needed)
for the inverse maps composed with a disc chart of `ℍ`. On an untouched collar, the extensions are
real on the diameter, hence conj-symmetric, hence bounded by the growth bound (the Koebe growth
estimate for the inverse doubled maps); Montel's theorem and the identity theorem identify the
limit.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Function
open scoped ComplexConjugate ComplexOrder

open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper (H Hbar)
open QuantumZipper.CA.Kernel (KernelConvergesTo)

namespace InteractingSLE

/-! ### Kernel convergence: generalities -/

section KernelGeneral

variable {G : ℕ → Set ℂ} {D : Set ℂ}

/-- The base point of a non-degenerate kernel limit can be any point of the limit domain. -/
theorem kernelConvergesTo_of_mem {w₀ w₁ : ℂ} (h : KernelConvergesTo G D w₀) (hD : D ≠ {w₀})
    (hw₁ : w₁ ∈ D) : KernelConvergesTo G D w₁ := by
  obtain ⟨h1 | ⟨hDo, hDc, hDu, -, hi⟩, hii⟩ := h
  · exact absurd h1 hD
  · exact ⟨Or.inr ⟨hDo, hDc, hDu, hw₁, hi⟩, hii⟩

/-- Condition (i) of kernel convergence for compact sets: a compact subset of the kernel lies in
all late domains. -/
theorem eventually_subset_of_isCompact {K : Set ℂ}
    (hi : ∀ w ∈ D, ∃ U ∈ 𝓝 w, ∀ᶠ n in atTop, U ⊆ G n) (hK : IsCompact K) (hKD : K ⊆ D) :
    ∀ᶠ n in atTop, K ⊆ G n := by
  choose! U hU hUev using hi
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover U (fun x hx => hU x (hKD hx))
  have hall : ∀ᶠ n in atTop, ∀ x ∈ t, U x ⊆ G n :=
    (Finset.eventually_all t).2 fun x hx => hUev x (hKD (htK x hx))
  filter_upwards [hall] with n hn z hz
  obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.1 (hcov hz)
  exact hn x hx hzx

/-- Condition (i) of non-degenerate kernel convergence. -/
theorem forall_exists_nhds_of_kernelConvergesTo {w₀ : ℂ} (h : KernelConvergesTo G D w₀)
    (hD : D ≠ {w₀}) : ∀ w ∈ D, ∃ U ∈ 𝓝 w, ∀ᶠ n in atTop, U ⊆ G n := by
  obtain ⟨h1 | ⟨-, -, -, -, hi⟩, -⟩ := h
  · exact absurd h1 hD
  · exact hi

end KernelGeneral

/-! ### Difference quotients and uniform convergence -/

section Dslope

/-- `dslope` is additive for functions differentiable at the base point. -/
theorem dslope_sub_eq {f g : ℂ → ℂ} {c : ℂ} (hf : DifferentiableAt ℂ f c)
    (hg : DifferentiableAt ℂ g c) (w : ℂ) :
    dslope (f - g) c w = dslope f c w - dslope g c w := by
  rcases eq_or_ne w c with rfl | hw
  · simp only [dslope_same]
    exact deriv_sub hf hg
  · simp only [dslope_of_ne _ hw, slope_def_field, Pi.sub_apply]
    ring

/-- **Maximum modulus bound for difference quotients**: if `h` is holomorphic on `B(0, r)` and
`‖h‖ ≤ ε` on `B̄(0, ρ)`, `0 < ρ < r`, then `‖(h w − h 0)/w‖ ≤ 2ε/ρ` on `B̄(0, ρ)`. -/
theorem norm_dslope_le {h : ℂ → ℂ} {ρ r ε : ℝ} (hρ : 0 < ρ) (hρr : ρ < r)
    (hd : DifferentiableOn ℂ h (ball 0 r)) (hε : ∀ z ∈ closedBall (0 : ℂ) ρ, ‖h z‖ ≤ ε)
    {w : ℂ} (hw : w ∈ closedBall (0 : ℂ) ρ) : ‖dslope h 0 w‖ ≤ 2 * ε / ρ := by
  have hdd : DifferentiableOn ℂ (dslope h 0) (ball 0 r) :=
    (Complex.differentiableOn_dslope (ball_mem_nhds 0 (hρ.trans hρr))).2 hd
  have hcl : DiffContOnCl ℂ (dslope h 0) (ball 0 ρ) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball 0 hρ.ne']
    exact hdd.mono (closedBall_subset_ball hρr)
  refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hcl (fun z hz => ?_)
    (by rw [closure_ball 0 hρ.ne']; exact hw)
  rw [frontier_ball 0 hρ.ne'] at hz
  have hzn : ‖z‖ = ρ := mem_sphere_zero_iff_norm.1 hz
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hzn
    linarith
  rw [dslope_of_ne _ hz0, slope_def_field, sub_zero, norm_div, hzn,
    div_le_div_iff_of_pos_right hρ]
  have h1 := hε z (sphere_subset_closedBall hz)
  have h2 := hε 0 (mem_closedBall_self hρ.le)
  calc ‖h z - h 0‖ ≤ ‖h z‖ + ‖h 0‖ := norm_sub_le _ _
    _ ≤ 2 * ε := by linarith

/-- **Uniform convergence of difference quotients**: if holomorphic functions on `B(0, r)`
converge uniformly on `B̄(0, ρ)`, `0 < ρ < r`, so do their difference quotients at `0`. -/
theorem tendstoUniformlyOn_dslope {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {ρ r : ℝ} (hρ : 0 < ρ)
    (hρr : ρ < r) (hF : ∀ n, DifferentiableOn ℂ (F n) (ball 0 r))
    (hf : DifferentiableOn ℂ f (ball 0 r))
    (hlim : TendstoUniformlyOn F f atTop (closedBall 0 ρ)) :
    TendstoUniformlyOn (fun n => dslope (F n) 0) (dslope f 0) atTop (closedBall 0 ρ) := by
  rw [Metric.tendstoUniformlyOn_iff] at hlim ⊢
  intro ε hε
  have h0 : ball (0 : ℂ) r ∈ 𝓝 0 := ball_mem_nhds 0 (hρ.trans hρr)
  filter_upwards [hlim (ε * ρ / 4) (by positivity)] with n hn w hw
  have heq : dslope (F n) 0 w - dslope f 0 w = dslope (F n - f) 0 w :=
    (dslope_sub_eq ((hF n).differentiableAt h0) (hf.differentiableAt h0) w).symm
  have hb := norm_dslope_le (ε := ε * ρ / 4) hρ hρr ((hF n).sub hf) (fun z hz => by
    have := hn z hz
    rw [dist_eq_norm, norm_sub_rev] at this
    exact this.le) hw
  rw [dist_eq_norm, norm_sub_rev, heq]
  calc ‖dslope (F n - f) 0 w‖ ≤ 2 * (ε * ρ / 4) / ρ := hb
    _ = ε / 2 := by field_simp; ring
    _ < ε := half_lt_self hε

end Dslope

/-! ### Uniform convergence: algebra -/

section UniformAlgebra

variable {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {K : Set ℂ}

/-- Inverses of uniformly convergent functions converge uniformly where the limit is bounded away
from `0`. -/
theorem tendstoUniformlyOn_inv {c : ℝ} (hc : 0 < c) (hf : ∀ z ∈ K, c ≤ ‖f z‖)
    (hlim : TendstoUniformlyOn F f atTop K) :
    TendstoUniformlyOn (fun n z => (F n z)⁻¹) (fun z => (f z)⁻¹) atTop K := by
  rw [Metric.tendstoUniformlyOn_iff] at hlim ⊢
  intro ε hε
  filter_upwards [hlim (min (c / 2) (ε * c ^ 2 / 2)) (by positivity)] with n hn z hz
  have h1 := hn z hz
  rw [dist_eq_norm] at h1
  have hfz := hf z hz
  have hFz : c / 2 ≤ ‖F n z‖ := by
    have : ‖f z‖ ≤ ‖f z - F n z‖ + ‖F n z‖ := by
      calc ‖f z‖ = ‖(f z - F n z) + F n z‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    linarith [min_le_left (c / 2) (ε * c ^ 2 / 2)]
  have hf0 : f z ≠ 0 := norm_pos_iff.1 (hc.trans_le hfz)
  have hF0 : F n z ≠ 0 := norm_pos_iff.1 ((half_pos hc).trans_le hFz)
  rw [dist_eq_norm, inv_sub_inv hf0 hF0, norm_div, norm_mul]
  have hden : c * (c / 2) ≤ ‖f z‖ * ‖F n z‖ :=
    mul_le_mul hfz hFz (by positivity) (norm_nonneg _)
  rw [div_lt_iff₀ (by positivity)]
  calc ‖F n z - f z‖ = ‖f z - F n z‖ := norm_sub_rev _ _
    _ < ε * c ^ 2 / 2 := h1.trans_le (min_le_right _ _)
    _ = ε * (c * (c / 2)) := by ring
    _ ≤ ε * (‖f z‖ * ‖F n z‖) := mul_le_mul_of_nonneg_left hden hε.le

/-- Affine combinations with convergent coefficients of a uniformly convergent sequence with a
bounded limit converge uniformly. -/
theorem tendstoUniformlyOn_const_mul_add {a b : ℕ → ℂ} {a₀ b₀ : ℂ} {M : ℝ}
    (hf : ∀ z ∈ K, ‖f z‖ ≤ M) (hlim : TendstoUniformlyOn F f atTop K)
    (ha : Tendsto a atTop (𝓝 a₀)) (hb : Tendsto b atTop (𝓝 b₀)) :
    TendstoUniformlyOn (fun n z => a n * F n z + b n) (fun z => a₀ * f z + b₀) atTop K := by
  rw [Metric.tendstoUniformlyOn_iff] at hlim ⊢
  intro ε hε
  set M' := max M 0 + 1 with hM'
  have hM'pos : 0 < M' := by positivity
  set A := ‖a₀‖ + 1 with hA
  have hApos : 0 < A := by positivity
  filter_upwards [hlim (ε / (4 * A)) (by positivity),
    (Metric.tendsto_nhds.1 ha) (min 1 (ε / (4 * M'))) (by positivity),
    (Metric.tendsto_nhds.1 hb) (ε / 4) (by positivity)] with n hn han hbn z hz
  rw [dist_eq_norm] at han hbn ⊢
  have h1 := hn z hz
  rw [dist_eq_norm] at h1
  have hfz : ‖f z‖ ≤ M' := (hf z hz).trans (by rw [hM']; linarith [le_max_left M 0])
  have han1 : ‖a n‖ ≤ A := by
    have : ‖a n‖ ≤ ‖a n - a₀‖ + ‖a₀‖ := by
      calc ‖a n‖ = ‖(a n - a₀) + a₀‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    linarith [min_le_left 1 (ε / (4 * M'))]
  have heq : a₀ * f z + b₀ - (a n * F n z + b n) =
      a n * (f z - F n z) + (a₀ - a n) * f z + (b₀ - b n) := by ring
  rw [heq]
  calc ‖a n * (f z - F n z) + (a₀ - a n) * f z + (b₀ - b n)‖
      ≤ ‖a n * (f z - F n z)‖ + ‖(a₀ - a n) * f z‖ + ‖b₀ - b n‖ := norm_add₃_le
    _ = ‖a n‖ * ‖f z - F n z‖ + ‖a n - a₀‖ * ‖f z‖ + ‖b n - b₀‖ := by
        rw [norm_mul, norm_mul, norm_sub_rev a₀, norm_sub_rev b₀]
    _ ≤ A * (ε / (4 * A)) + (ε / (4 * M')) * M' + ε / 4 := by
        exact add_le_add (add_le_add (mul_le_mul han1 h1.le (norm_nonneg _) hApos.le)
          (mul_le_mul (han.le.trans (min_le_right _ _)) hfz (norm_nonneg _) (by positivity)))
          hbn.le
    _ = 3 * ε / 4 := by field_simp; ring
    _ < ε := by linarith

end UniformAlgebra

/-! ### The explicit mapping-out function of the doubling -/

section MapOutExplicit

/-- The symmetric normalized Riemann map of the doubled domain (`exists_dblRiemann`). -/
def IsDblRiemann (A : Set ℂ) (R : ℝ) (F : ℂ → ℂ) : Prop :=
  IsConformalBijection F (dblΩ A R) (ball 0 1) ∧ F 0 = 0 ∧ 0 < (deriv F 0).re ∧
    (deriv F 0).im = 0 ∧ ∀ w ∈ dblΩ A R, F (conj w) = conj (F w)

theorem exists_isDblRiemann {A : Set ℂ} {R : ℝ} (hA : IsHPHull A) (hR : 0 < R)
    (hAR : A ⊆ ball 0 R) : ∃ F, IsDblRiemann A R F :=
  exists_dblRiemann hA hR hAR

/-- **The mapping-out function is explicit in the symmetric Riemann map of the doubling**: for
every `F` as in `exists_dblRiemann`, `MapOutConstruction.mapOut R F` is the mapping-out function of
`A`, and `z (g z − z) → −Re r'(0)` for the remainder `r`. This is the proof of
`IsHPHull.exists_isMapOut_tendsto` (`HullExists.lean`) for a given `F`; that statement hides `F`. -/
theorem isMapOut_mapOut {A : Set ℂ} {R : ℝ} {F : ℂ → ℂ} (hA : IsHPHull A) (hR : 0 < R)
    (hAR : A ⊆ ball 0 R) (hFR : IsDblRiemann A R F) :
    IsMapOut A (MapOutConstruction.mapOut R F) ∧
      Tendsto (fun z => z * (MapOutConstruction.mapOut R F z - z))
        (Bornology.cobounded ℂ ⊓ 𝓟 (H \ A))
        (𝓝 ((-(deriv (MapOutConstruction.remainder F) 0).re : ℝ) : ℂ)) := by
  obtain ⟨hF, hF0, hFre, hFim, hsym⟩ := hFR
  have hup := bijOn_dblRiemann_upper hA hR hAR hF hF0 hFre hsym
  set δ : ℝ := 1 / (4 * R) with hδ
  have hδpos : 0 < δ := by positivity
  have hBΩ : ball (0 : ℂ) δ ⊆ dblΩ A R := ball_subset_dblΩ hR hAR
  have hFd : DifferentiableOn ℂ F (ball 0 δ) := hF.1.mono hBΩ
  have hinj : InjOn F (ball 0 δ) := hF.2.injOn.mono hBΩ
  have hc0 : deriv F 0 ≠ 0 := fun h => by rw [h] at hFre; simp at hFre
  have hre : ∀ t : ℝ, |t| < δ → (F t).im = 0 := by
    intro t ht
    have htΩ : (t : ℂ) ∈ dblΩ A R := hBΩ (by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact ht)
    have := hsym _ htΩ
    rw [conj_ofReal] at this
    exact Complex.conj_eq_iff_im.1 this.symm
  set r := MapOutConstruction.remainder F with hrdef
  have hrd := MapOutConstruction.differentiableOn_remainder hδpos hFd hF0 hc0 hinj
  have hr0 : r 0 = 0 := MapOutConstruction.remainder_zero hF0
  have hrre := MapOutConstruction.im_remainder_eq_zero hδpos hFd hF0 hFim hre
  have hrD : HasDerivAt r (deriv r 0) 0 :=
    (hrd.differentiableAt (ball_mem_nhds 0 hδpos)).hasDerivAt
  have hrim : (deriv r 0).im = 0 := im_deriv_eq_zero_of_im_eq_zero hδpos hrD.differentiableAt hrre
  have hq0 : (MapOutConstruction.quot F 0).im = 0 := by
    have := MapOutConstruction.im_quot_eq_zero hδpos hFd hF0 hFim hre 0 (by simpa using hδpos)
    rwa [ofReal_zero] at this
  set p : ℂ := ((2 * R : ℝ) : ℂ) with hp
  set g := MapOutConstruction.mapOut R F with hgdef
  set S := H \ A with hSdef
  -- conformal bijection
  have hιd : DifferentiableOn ℂ (dblι R) S := by
    intro z hz
    have hz0 : p - z ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      have hz' : 0 < z.im := hz.1
      simp [hp] at this; linarith
    exact ((differentiableAt_const _).sub differentiableAt_id).inv hz0 |>.differentiableWithinAt
  have hmapsι : MapsTo (dblι R) S (dblΩ A R ∩ H) := (bijOn_dblι hA).mapsTo
  have hgd : DifferentiableOn ℂ g S := by
    have h1 : DifferentiableOn ℂ (fun z => F (dblι R z)) S :=
      (hF.1.mono inter_subset_left).comp hιd hmapsι
    have h2 : DifferentiableOn ℂ (fun z => joukowski (F (dblι R z))) S :=
      differentiableOn_joukowski.comp h1 fun z hz => hup.mapsTo (hmapsι hz)
    exact (h2.const_mul _).sub_const _
  have hgb : BijOn g S H := by
    have hb := (QuantumZipper.CA.bijOn_affine_H (a := 2 * (deriv F 0).re)
      (b := -(MapOutConstruction.quot F 0 - p).re) (by linarith)).comp
      (bijOn_joukowski.comp (hup.comp (bijOn_dblι hA)))
    refine hb.congr fun z _ => ?_
    simp only [Function.comp_apply, hgdef, MapOutConstruction.mapOut]
    rw [MapOutConstruction.eq_ofReal_re_of_im_eq_zero hFim]
    have hβ : (MapOutConstruction.quot F 0 - p) =
        (((MapOutConstruction.quot F 0 - p).re : ℝ) : ℂ) :=
      MapOutConstruction.eq_ofReal_re_of_im_eq_zero (by simp [hp, hq0])
    conv_rhs => rw [hβ]
    simp only [ofReal_re]
    push_cast
    ring
  -- the expansion
  have hpz : Tendsto (fun z => p - z) (Bornology.cobounded ℂ ⊓ 𝓟 S) (Bornology.cobounded ℂ) := by
    refine tendsto_norm_atTop_iff_cobounded.1 (tendsto_atTop_mono (fun z => ?_)
      (tendsto_atTop_add_const_right _ (-‖p‖)
        (tendsto_norm_cobounded_atTop.mono_left inf_le_left)))
    have := norm_sub_norm_le z p
    rw [norm_sub_rev] at this
    linarith
  have hι : Tendsto (dblι R) (Bornology.cobounded ℂ ⊓ 𝓟 S) (𝓝[≠] 0) :=
    tendsto_inv₀_cobounded'.comp hpz
  have hι' : Tendsto (dblι R) (Bornology.cobounded ℂ ⊓ 𝓟 S) (𝓝 0) :=
    hι.mono_right nhdsWithin_le_nhds
  have hev : ∀ᶠ z in Bornology.cobounded ℂ ⊓ 𝓟 S, g z - z = r (dblι R z) := by
    filter_upwards [hι'.eventually (ball_mem_nhds 0 hδpos), mem_inf_of_right (mem_principal_self S)]
      with z hzB hzS
    have h1 := MapOutConstruction.mapOut_eq R hF0 hc0 hinj hzB (dblι_ne_zero hzS.1)
    rw [sub_inv_dblι] at h1
    simp only [hgdef, MapOutConstruction.mapOut]
    rw [h1]; ring
  have hlim0 : Tendsto (fun z => r (dblι R z)) (Bornology.cobounded ℂ ⊓ 𝓟 S) (𝓝 0) := by
    have := hrD.continuousAt.tendsto.comp hι'
    rwa [hr0] at this
  have hslope : Tendsto (fun ζ => ζ⁻¹ * r ζ) (𝓝[≠] 0) (𝓝 (deriv r 0)) := by
    have := hrD.tendsto_slope_zero
    simpa [hr0] using this
  refine ⟨⟨⟨hgd, hgb⟩, (hlim0.congr' (hev.mono fun z h => h.symm))⟩, ?_⟩
  have hT : Tendsto (fun z => p * r (dblι R z) - (dblι R z)⁻¹ * r (dblι R z))
      (Bornology.cobounded ℂ ⊓ 𝓟 S) (𝓝 (p * 0 - deriv r 0)) :=
    (hlim0.const_mul p).sub (hslope.comp hι)
  have hval : p * 0 - deriv r 0 = ((-(deriv r 0).re : ℝ) : ℂ) := by
    rw [mul_zero, zero_sub, ofReal_neg, ← MapOutConstruction.eq_ofReal_re_of_im_eq_zero hrim]
  rw [hval] at hT
  refine hT.congr' ?_
  filter_upwards [hev] with z hz
  rw [hz]
  have hz' : p - (dblι R z)⁻¹ = z := sub_inv_dblι
  calc p * r (dblι R z) - (dblι R z)⁻¹ * r (dblι R z)
      = (p - (dblι R z)⁻¹) * r (dblι R z) := by ring
    _ = z * r (dblι R z) := by rw [hz']


end MapOutExplicit

/-! ### Kernel convergence of the doubled domains -/

section DoubledKernel

variable {A : ℕ → Set ℂ} {B : Set ℂ} {R : ℝ}

/-- The complement of a hull is never a singleton (it is open). -/
theorem IsHPHull.H_diff_ne_singleton {B : Set ℂ} (hB : IsHPHull B) (w : ℂ) : H \ B ≠ {w} :=
  fun h => not_isOpen_singleton w (h ▸ hB.isOpen)

theorem mem_dblΩ_iff_of_ne {A : Set ℂ} {w : ℂ} (hw : w ≠ 0) :
    w ∈ dblΩ A R ↔ ((2 * R : ℝ) : ℂ) - w⁻¹ ∉ dblK A R :=
  ⟨fun h => h.resolve_left hw, fun h => Or.inr h⟩

theorem zero_mem_dblΩ {A : Set ℂ} : (0 : ℂ) ∈ dblΩ A R := Or.inl rfl

theorem continuousAt_sub_inv {w : ℂ} (hw : w ≠ 0) :
    ContinuousAt (fun w : ℂ => ((2 * R : ℝ) : ℂ) - w⁻¹) w :=
  continuousAt_const.sub (continuousAt_inv₀ hw)

/-- A point of `ℍ \ B` has a neighbourhood avoiding the late doubled hulls. -/
theorem exists_nhds_notMem_dblK_of_mem_H {w₀ : ℂ} (hA : ∀ n, IsHPHull (A n)) (hB : IsHPHull B)
    (hker : KernelConvergesTo (fun n => H \ A n) (H \ B) w₀) {z : ℂ} (hzH : z ∈ H)
    (hzB : z ∉ B) : ∃ V ∈ 𝓝 z, ∀ᶠ n in atTop, ∀ y ∈ V, y ∉ dblK (A n) R := by
  obtain ⟨U, hU, hev⟩ :=
    forall_exists_nhds_of_kernelConvergesTo hker (hB.H_diff_ne_singleton w₀) z ⟨hzH, hzB⟩
  refine ⟨U ∩ H, inter_mem hU (QuantumZipper.isOpen_H.mem_nhds hzH), ?_⟩
  filter_upwards [hev] with n hn y hy
  exact dblK_disjoint_H (hA n) hy.2 (hn hy.1).2

/-- A point outside the doubled limit hull has a neighbourhood avoiding the late doubled hulls. -/
theorem exists_nhds_notMem_dblK {w₀ : ℂ} (hA : ∀ n, IsHPHull (A n)) (hB : IsHPHull B)
    (hR : 0 < R) (hAR : ∀ n, A n ⊆ ball 0 R)
    (hker : KernelConvergesTo (fun n => H \ A n) (H \ B) w₀) {z : ℂ} (hz : z ∉ dblK B R) :
    ∃ V ∈ 𝓝 z, ∀ᶠ n in atTop, ∀ y ∈ V, y ∉ dblK (A n) R := by
  have hzB : z ∉ B := fun h => hz (Or.inl (Or.inl h))
  have hczB : conj z ∉ B := fun h => hz (Or.inl (Or.inr h))
  rcases lt_trichotomy z.im 0 with h | h | h
  · obtain ⟨V, hV, hev⟩ := exists_nhds_notMem_dblK_of_mem_H (R := R) hA hB hker
      (show 0 < (conj z).im by simp; linarith) hczB
    refine ⟨(fun y => conj y) ⁻¹' V, Complex.continuous_conj.continuousAt.preimage_mem_nhds
      (by simpa using hV), ?_⟩
    filter_upwards [hev] with n hn y hy
    exact fun hyK => hn _ hy (conj_mem_dblK_iff.2 hyK)
  · have hre : 2 * R < |z.re| := by
      by_contra hle
      exact hz (Or.inr ⟨h, not_lt.1 hle⟩)
    have hzn : 2 * R < ‖z‖ := hre.trans_le (Complex.abs_re_le_norm z)
    refine ⟨{y | 2 * R < ‖y‖}, (isOpen_lt continuous_const continuous_norm).mem_nhds hzn,
      Eventually.of_forall fun n y hy hyK => ?_⟩
    have := mem_closedBall_zero_iff.1 (dblK_subset_closedBall hR (hAR n) hyK)
    exact absurd hy (not_lt.2 this)
  · exact exists_nhds_notMem_dblK_of_mem_H hA hB hker h hzB

/-- Condition (i) for the doubled domains. -/
theorem exists_nhds_subset_dblΩ {w₀ : ℂ} (hA : ∀ n, IsHPHull (A n)) (hB : IsHPHull B)
    (hR : 0 < R) (hAR : ∀ n, A n ⊆ ball 0 R)
    (hker : KernelConvergesTo (fun n => H \ A n) (H \ B) w₀) {w : ℂ} (hw : w ∈ dblΩ B R) :
    ∃ U ∈ 𝓝 w, ∀ᶠ n in atTop, U ⊆ dblΩ (A n) R := by
  by_cases hw0 : w = 0
  · subst hw0
    exact ⟨ball 0 (1 / (4 * R)), ball_mem_nhds 0 (by positivity),
      Eventually.of_forall fun n => ball_subset_dblΩ hR (hAR n)⟩
  obtain ⟨V, hV, hev⟩ := exists_nhds_notMem_dblK hA hB hR hAR hker
    ((mem_dblΩ_iff_of_ne hw0).1 hw)
  refine ⟨{y | y ≠ 0} ∩ (fun y : ℂ => ((2 * R : ℝ) : ℂ) - y⁻¹) ⁻¹' V,
    inter_mem (isOpen_ne.mem_nhds hw0) ((continuousAt_sub_inv hw0).preimage_mem_nhds hV), ?_⟩
  filter_upwards [hev] with n hn y hy
  exact (mem_dblΩ_iff_of_ne hy.1).2 (hn _ hy.2)

/-- Near a frontier point of the doubled limit domain coming from `B`, the late doubled domains
have complementary points. -/
theorem eventually_exists_notMem_dblΩ_of_mem {w₀ : ℂ} (hA : ∀ n, IsHPHull (A n))
    (hB : IsHPHull B) (hker : KernelConvergesTo (fun n => H \ A n) (H \ B) w₀) {p : ℂ}
    (hp0 : p ≠ 0) (hpc : p ∈ closure (dblΩ B R)) (hpB : ((2 * R : ℝ) : ℂ) - p⁻¹ ∈ B) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ n in atTop, ∃ y ∈ ball p ε, y ∉ dblΩ (A n) R := by
  set z := ((2 * R : ℝ) : ℂ) - p⁻¹ with hz
  have hzH : z ∈ H := hB.1 hpB
  have hp2 : ((2 * R : ℝ) : ℂ) - z = p⁻¹ := by rw [hz]; ring
  -- `z` is a frontier point of `ℍ \ B`
  have hzc : z ∈ closure (H \ B) := by
    have h1 : z ∈ closure ((fun w : ℂ => ((2 * R : ℝ) : ℂ) - w⁻¹) '' dblΩ B R) :=
      (continuousAt_sub_inv hp0).continuousWithinAt.mem_closure_image hpc
    have h2 : (fun w : ℂ => ((2 * R : ℝ) : ℂ) - w⁻¹) '' dblΩ B R ⊆
        (dblK B R)ᶜ ∪ {((2 * R : ℝ) : ℂ)} := by
      rintro _ ⟨w, hw, rfl⟩
      by_cases hw0 : w = 0
      · right; simp [hw0]
      · left; exact (mem_dblΩ_iff_of_ne hw0).1 hw
    have h3 := closure_mono h2 h1
    rw [closure_union, closure_singleton] at h3
    have hz2 : z ≠ ((2 * R : ℝ) : ℂ) := fun h => by
      have : (0 : ℝ) < z.im := hzH
      rw [h] at this; simp at this
    have h4 : z ∈ closure (dblK B R)ᶜ := h3.resolve_right hz2
    have h5 := QuantumZipper.isOpen_H.inter_closure ⟨hzH, h4⟩
    refine closure_mono ?_ h5
    exact fun y hy => ⟨hy.1, fun hyB => hy.2 (Or.inl (Or.inl hyB))⟩
  have hzf : z ∈ frontier (H \ B) := by
    rw [frontier, hB.isOpen.interior_eq]
    exact ⟨hzc, fun h => h.2 hpB⟩
  obtain ⟨u, hu, hut⟩ := hker.2 z hzf
  have hev1 : ∀ᶠ n in atTop, u n ∈ H := hut.eventually (QuantumZipper.isOpen_H.mem_nhds hzH)
  have hcont : ContinuousAt (fun w => (((2 * R : ℝ) : ℂ) - w)⁻¹) z :=
    (continuousAt_const.sub continuousAt_id).inv₀
      (show ((2 * R : ℝ) : ℂ) - z ≠ 0 by rw [hp2]; exact inv_ne_zero hp0)
  have hval : (((2 * R : ℝ) : ℂ) - z)⁻¹ = p := by rw [hp2, inv_inv]
  have hyt : Tendsto (fun n => dblι R (u n)) atTop (𝓝 p) := hval ▸ hcont.tendsto.comp hut
  filter_upwards [hev1, hyt.eventually (ball_mem_nhds p hε)] with n hn1 hn2
  refine ⟨dblι R (u n), hn2, fun hmem => ?_⟩
  have hu_notin : u n ∉ H \ A n := notMem_of_mem_frontier (hA n).isOpen (hu n)
  have huA : u n ∈ A n := by
    by_contra h
    exact hu_notin ⟨hn1, h⟩
  rcases hmem with h | h
  · exact dblι_ne_zero hn1 h
  · exact h (by rw [sub_inv_dblι]; exact Or.inl (Or.inl huA))

/-- **Kernel convergence passes to the doubled domains**: if `ℍ \ A n → ℍ \ B` and all hulls lie in
`B(0, R)`, then `dblΩ (A n) R → dblΩ B R` with respect to `0`. -/
theorem kernelConvergesTo_dblΩ {w₀ : ℂ} (hA : ∀ n, IsHPHull (A n)) (hB : IsHPHull B)
    (hR : 0 < R) (hAR : ∀ n, A n ⊆ ball 0 R) (hBR : B ⊆ ball 0 R)
    (hker : KernelConvergesTo (fun n => H \ A n) (H \ B) w₀) :
    KernelConvergesTo (fun n => dblΩ (A n) R) (dblΩ B R) 0 := by
  have hΩo := isOpen_dblΩ hB hR hBR
  refine ⟨Or.inr ⟨hΩo, isConnected_dblΩ hB hR hBR, dblΩ_ne_univ hR, zero_mem_dblΩ,
    fun w hw => exists_nhds_subset_dblΩ hA hB hR hAR hker hw⟩, fun p hp => ?_⟩
  have hpΩ : p ∉ dblΩ B R := notMem_of_mem_frontier hΩo hp
  have hp0 : p ≠ 0 := fun h => hpΩ (h ▸ zero_mem_dblΩ)
  have hpK : ((2 * R : ℝ) : ℂ) - p⁻¹ ∈ dblK B R := by
    by_contra h
    exact hpΩ ((mem_dblΩ_iff_of_ne hp0).2 h)
  have hpc : p ∈ closure (dblΩ B R) := frontier_subset_closure hp
  refine exists_tendsto_frontier
    (fun n => frontier_nonempty_of_isOpen
      (Set.nonempty_of_mem (zero_mem_dblΩ (A := A n) (R := R))) (dblΩ_ne_univ hR)) fun ε hε => ?_
  obtain ⟨x, hxb, hxΩ⟩ : ∃ x ∈ ball p ε, x ∈ dblΩ B R := by
    obtain ⟨x, hx1, hx2⟩ := Metric.mem_closure_iff.1 hpc ε hε
    exact ⟨x, by rw [mem_ball, dist_comm]; exact hx2, hx1⟩
  obtain ⟨U, hU, hUev⟩ := exists_nhds_subset_dblΩ hA hB hR hAR hker hxΩ
  have hy : ∀ᶠ n in atTop, ∃ y ∈ ball p ε, y ∉ dblΩ (A n) R := by
    rcases hpK with (h | h) | h
    · exact eventually_exists_notMem_dblΩ_of_mem hA hB hker hp0 hpc h hε
    · have hcp0 : conj p ≠ 0 := (map_ne_zero _).2 hp0
      have hcpc : conj p ∈ closure (dblΩ B R) :=
        map_mem_closure Complex.continuous_conj hpc fun w hw => conj_mem_dblΩ_iff.2 hw
      have hcpB : ((2 * R : ℝ) : ℂ) - (conj p)⁻¹ ∈ B := by
        rwa [show ((2 * R : ℝ) : ℂ) - (conj p)⁻¹ = conj (((2 * R : ℝ) : ℂ) - p⁻¹) by
          rw [map_sub, map_inv₀, conj_ofReal]]
      filter_upwards [eventually_exists_notMem_dblΩ_of_mem hA hB hker hcp0 hcpc hcpB hε]
        with n hn
      obtain ⟨y, hyb, hyΩ⟩ := hn
      refine ⟨conj y, ?_, fun h => hyΩ ?_⟩
      · rw [mem_ball] at hyb ⊢
        rwa [← dist_conj_conj, conj_conj]
      · have := conj_mem_dblΩ_iff.2 h
        rwa [conj_conj] at this
    · exact Eventually.of_forall fun n =>
        ⟨p, mem_ball_self hε, fun hpn => ((mem_dblΩ_iff_of_ne hp0).1 hpn) (Or.inr h)⟩
  filter_upwards [hUev, hy] with n hn hyn
  obtain ⟨y, hyb, hyΩ⟩ := hyn
  exact ball_inter_frontier_nonempty (isOpen_dblΩ (hA n) hR (hAR n)) hxb
    (hn (mem_of_mem_nhds hU)) hyb hyΩ

end DoubledKernel

/-! ### More uniform algebra -/

section UniformAlgebra2

variable {F G : ℕ → ℂ → ℂ} {f g : ℂ → ℂ} {K : Set ℂ}

/-- Products of uniformly convergent sequences with bounded limits converge uniformly. -/
theorem tendstoUniformlyOn_mul {M N : ℝ} (hf : ∀ z ∈ K, ‖f z‖ ≤ M) (hg : ∀ z ∈ K, ‖g z‖ ≤ N)
    (hF : TendstoUniformlyOn F f atTop K) (hG : TendstoUniformlyOn G g atTop K) :
    TendstoUniformlyOn (fun n z => F n z * G n z) (fun z => f z * g z) atTop K := by
  rw [Metric.tendstoUniformlyOn_iff] at hF hG ⊢
  intro ε hε
  set M' := max M 0 + 1 with hM'
  set N' := max N 0 + 1 with hN'
  have hM'pos : 0 < M' := by positivity
  have hN'pos : 0 < N' := by positivity
  filter_upwards [hF (min 1 (ε / (4 * N'))) (by positivity),
    hG (ε / (4 * (M' + 1))) (by positivity)]
    with n hFn hGn z hz
  have h1 := hFn z hz
  have h2 := hGn z hz
  rw [dist_eq_norm] at h1 h2 ⊢
  have hfz : ‖f z‖ ≤ M' := (hf z hz).trans (by rw [hM']; linarith [le_max_left M 0])
  have hgz : ‖g z‖ ≤ N' := (hg z hz).trans (by rw [hN']; linarith [le_max_left N 0])
  have hFz : ‖F n z‖ ≤ M' + 1 := by
    have : ‖F n z‖ ≤ ‖f z‖ + ‖f z - F n z‖ := by
      calc ‖F n z‖ = ‖f z - (f z - F n z)‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    linarith [min_le_left 1 (ε / (4 * N'))]
  have heq : f z * g z - F n z * G n z = F n z * (g z - G n z) + (f z - F n z) * g z := by ring
  rw [heq]
  calc ‖F n z * (g z - G n z) + (f z - F n z) * g z‖
      ≤ ‖F n z‖ * ‖g z - G n z‖ + ‖f z - F n z‖ * ‖g z‖ := by
        rw [← norm_mul, ← norm_mul]; exact norm_add_le _ _
    _ ≤ (M' + 1) * (ε / (4 * (M' + 1))) + (ε / (4 * N')) * N' :=
        add_le_add (mul_le_mul hFz h2.le (norm_nonneg _) (by positivity))
          (mul_le_mul (h1.le.trans (min_le_right _ _)) hgz (norm_nonneg _) (by positivity))
    _ = ε / 2 := by field_simp; ring
    _ < ε := half_lt_self hε

/-- A function continuous and nonvanishing on a compact set is bounded away from `0` there. -/
theorem exists_pos_le_norm_of_continuousOn {u : ℂ → ℂ} (hK : IsCompact K) (hu : ContinuousOn u K)
    (hu0 : ∀ z ∈ K, u z ≠ 0) : ∃ c > 0, ∀ z ∈ K, c ≤ ‖u z‖ := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hu.inv₀ hu0)
  refine ⟨1 / (max C 0 + 1), by positivity, fun z hz => ?_⟩
  have h1 : ‖(u z)⁻¹‖ ≤ C := hC z hz
  rw [norm_inv] at h1
  have hpos : 0 < ‖u z‖ := norm_pos_iff.2 (hu0 z hz)
  rw [div_le_iff₀ (by positivity)]
  have h2 : (‖u z‖)⁻¹ ≤ max C 0 + 1 := h1.trans (by linarith [le_max_left C 0])
  have h3 := (inv_le_iff_one_le_mul₀' hpos).1 h2
  linarith

end UniformAlgebra2

/-! ### Convergence of the explicit mapping-out functions -/

section MapOutConvergence

open MapOutConstruction

/-- The inverse of a normalized chart `U → 𝔻` is a normalized conformal map `𝔻 → U`
(QuantumZipper's `modelPullback_props`). -/
theorem isConformalBijection_invFunOn_ball {U : Set ℂ} (hUo : IsOpen U) {F : ℂ → ℂ} {a : ℂ}
    (hF : IsConformalBijection F U (ball 0 1)) (ha : a ∈ U) (hF0 : F a = 0)
    (hF' : 0 < deriv F a) :
    IsConformalBijection (invFunOn F U) (ball 0 1) U ∧ invFunOn F U 0 = a ∧
      0 < deriv (invFunOn F U) 0 := by
  obtain ⟨hd, hi, him', h0, h'⟩ := QuantumZipper.CA.Kernel.modelPullback_props (S := id)
    differentiableOn_id (injOn_id _) (image_id _) rfl (by simp) hUo hF.1 hF.2 ha hF0 hF'
  have hb := hi.bijOn_image
  rw [him'] at hb
  exact ⟨⟨hd, hb⟩, h0, h'⟩

theorem IsDblRiemann.deriv_pos {A : Set ℂ} {R : ℝ} {F : ℂ → ℂ} (h : IsDblRiemann A R F) :
    0 < deriv F 0 :=
  Complex.pos_iff.2 ⟨h.2.2.1, h.2.2.2.1.symm⟩

theorem IsDblRiemann.deriv_ne_zero {A : Set ℂ} {R : ℝ} {F : ℂ → ℂ} (h : IsDblRiemann A R F) :
    deriv F 0 ≠ 0 :=
  h.deriv_pos.ne'

variable {A : ℕ → Set ℂ} {B : Set ℂ} {R : ℝ} {F : ℕ → ℂ → ℂ} {F₀ : ℂ → ℂ}

/-- **Convergence of the symmetric Riemann maps of the doubled domains** (disc kernel theorem for
their inverses, then QuantumZipper's `tendstoUniformlyOn_of_invFunOn`). -/
theorem tendstoLocallyUniformlyOn_dblRiemann {w₀ : ℂ} (hA : ∀ n, IsHPHull (A n))
    (hB : IsHPHull B) (hR : 0 < R) (hAR : ∀ n, A n ⊆ ball 0 R) (hBR : B ⊆ ball 0 R)
    (hker : KernelConvergesTo (fun n => H \ A n) (H \ B) w₀)
    (hF : ∀ n, IsDblRiemann (A n) R (F n)) (hF₀ : IsDblRiemann B R F₀) :
    TendstoLocallyUniformlyOn F F₀ atTop (dblΩ B R) := by
  have hkΩ := kernelConvergesTo_dblΩ hA hB hR hAR hBR hker
  have hΩo : ∀ n, IsOpen (dblΩ (A n) R) := fun n => isOpen_dblΩ (hA n) hR (hAR n)
  have hΩBo := isOpen_dblΩ hB hR hBR
  have hinv := fun n => isConformalBijection_invFunOn_ball (hΩo n) (hF n).1 zero_mem_dblΩ
    (hF n).2.1 (hF n).deriv_pos
  have hinv₀ := isConformalBijection_invFunOn_ball hΩBo hF₀.1 zero_mem_dblΩ hF₀.2.1
    hF₀.deriv_pos
  have hlim : TendstoLocallyUniformlyOn (fun n => invFunOn (F n) (dblΩ (A n) R))
      (invFunOn F₀ (dblΩ B R)) atTop (ball 0 1) :=
    (kernel_convergence_iff (fun n => (hinv n).1) (fun n => (hinv n).2.1)
      (fun n => (hinv n).2.2) (Or.inr hinv₀)).2 hkΩ
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hΩBo]
  intro K hKΩ hK
  exact QuantumZipper.CA.Kernel.tendstoUniformlyOn_of_invFunOn isOpen_ball
    (fun n => (hF n).1.2) hF₀.1.2
    (fun z hz => (hF₀.1.1.differentiableAt (hΩBo.mem_nhds hz)).continuousAt)
    (fun n => (hinv n).1.1) hinv₀.1.2.injOn hlim hK hKΩ

end MapOutConvergence

/-! ### Convergence of the coefficients -/

section Coefficients

open MapOutConstruction

variable {F : ℕ → ℂ → ℂ} {F₀ : ℂ → ℂ} {δ : ℝ}

/-- **The coefficients of the explicit mapping-out function converge**: if univalent `F n`,
`F n 0 = 0`, converge uniformly on `B̄(0, δ/2)` to `F₀` with `F₀'(0) ≠ 0`, then `F n'(0)`,
`P_n(0) = κ₂(0)/κ(0)` and the derivative at `0` of the remainder converge. -/
theorem tendsto_coeffs_of_tendstoUniformlyOn (hδ : 0 < δ)
    (hFd : ∀ n, DifferentiableOn ℂ (F n) (ball 0 δ)) (hFi : ∀ n, InjOn (F n) (ball 0 δ))
    (hF0 : ∀ n, F n 0 = 0) (hFc : ∀ n, deriv (F n) 0 ≠ 0)
    (hF₀d : DifferentiableOn ℂ F₀ (ball 0 δ)) (hF₀i : InjOn F₀ (ball 0 δ)) (hF₀0 : F₀ 0 = 0)
    (hF₀c : deriv F₀ 0 ≠ 0) (hlim : TendstoUniformlyOn F F₀ atTop (closedBall 0 (δ / 2))) :
    Tendsto (fun n => deriv (F n) 0) atTop (𝓝 (deriv F₀ 0)) ∧
      Tendsto (fun n => quot (F n) 0) atTop (𝓝 (quot F₀ 0)) ∧
      Tendsto (fun n => deriv (remainder (F n)) 0) atTop (𝓝 (deriv (remainder F₀) 0)) := by
  set ρ := δ / 2 with hρdef
  have hρ : 0 < ρ := half_pos hδ
  have hρδ : ρ < δ := half_lt_self hδ
  have h0 : (0 : ℂ) ∈ closedBall (0 : ℂ) ρ := mem_closedBall_self hρ.le
  have hκ : TendstoUniformlyOn (fun n => kappa (F n)) (kappa F₀) atTop (closedBall 0 ρ) :=
    tendstoUniformlyOn_dslope hρ hρδ hFd hF₀d hlim
  have hκ2 : TendstoUniformlyOn (fun n => kappa2 (F n)) (kappa2 F₀) atTop (closedBall 0 ρ) :=
    tendstoUniformlyOn_dslope hρ hρδ (fun n => differentiableOn_kappa hδ (hFd n))
      (differentiableOn_kappa hδ hF₀d) hκ
  have hd : Tendsto (fun n => deriv (F n) 0) atTop (𝓝 (deriv F₀ 0)) := by
    have := hκ.tendsto_at h0
    simpa only [kappa_zero] using this
  have hκ0 : kappa F₀ 0 ≠ 0 := by rw [kappa_zero]; exact hF₀c
  have hq : Tendsto (fun n => quot (F n) 0) atTop (𝓝 (quot F₀ 0)) :=
    (hκ2.tendsto_at h0).div (hκ.tendsto_at h0) hκ0
  refine ⟨hd, hq, ?_⟩
  -- a closed disc on which `κ₀` is bounded away from `0`
  have hκc : ContinuousAt (kappa F₀) 0 :=
    (differentiableOn_kappa hδ hF₀d).continuousOn.continuousAt (ball_mem_nhds 0 hδ)
  obtain ⟨η, hη, hηκ⟩ := Metric.continuousAt_iff.1 hκc (‖kappa F₀ 0‖ / 2)
    (by have := norm_pos_iff.2 hκ0; positivity)
  set ρ' := min ρ (η / 2) with hρ'def
  have hρ' : 0 < ρ' := lt_min hρ (half_pos hη)
  have hρ'ρ : ρ' ≤ ρ := min_le_left _ _
  have hsub : closedBall (0 : ℂ) ρ' ⊆ closedBall 0 ρ := closedBall_subset_closedBall hρ'ρ
  have hlow : ∀ w ∈ closedBall (0 : ℂ) ρ', ‖kappa F₀ 0‖ / 2 ≤ ‖kappa F₀ w‖ := by
    intro w hw
    have hw' : dist w 0 < η := by
      rw [mem_closedBall] at hw
      linarith [min_le_right ρ (η / 2)]
    have h1 := hηκ hw'
    rw [dist_eq_norm] at h1
    have : ‖kappa F₀ 0‖ ≤ ‖kappa F₀ w‖ + ‖kappa F₀ w - kappa F₀ 0‖ := by
      calc ‖kappa F₀ 0‖ = ‖kappa F₀ w - (kappa F₀ w - kappa F₀ 0)‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    linarith
  have hcpos : 0 < ‖kappa F₀ 0‖ / 2 := by have := norm_pos_iff.2 hκ0; positivity
  have hcB : IsCompact (closedBall (0 : ℂ) ρ') := isCompact_closedBall 0 ρ'
  have hcont : ∀ {f : ℂ → ℂ}, DifferentiableOn ℂ f (ball 0 δ) →
      ∃ M, ∀ z ∈ closedBall (0 : ℂ) ρ', ‖f z‖ ≤ M := fun hf =>
    hcB.exists_bound_of_continuousOn
      (hf.continuousOn.mono ((closedBall_subset_ball (hρ'ρ.trans_lt hρδ))))
  obtain ⟨M₂, hM₂⟩ := hcont (differentiableOn_kappa2 hδ hF₀d)
  obtain ⟨M₀, hM₀⟩ := hcont hF₀d
  have hinv := tendstoUniformlyOn_inv hcpos hlow (hκ.mono hsub)
  have hquot : TendstoUniformlyOn (fun n => quot (F n)) (quot F₀) atTop (closedBall 0 ρ') :=
    tendstoUniformlyOn_mul (M := M₂) (N := (‖kappa F₀ 0‖ / 2)⁻¹) hM₂
      (fun z hz => by
        rw [norm_inv]
        exact inv_anti₀ hcpos (hlow z hz)) (hκ2.mono hsub) hinv
  have hrest := tendstoUniformlyOn_const_mul_add hM₀ (hlim.mono hsub) hd.neg hq.neg
  have hrem : TendstoUniformlyOn (fun n => remainder (F n)) (remainder F₀) atTop
      (closedBall 0 ρ') := by
    refine ((hquot.add hrest).congr (Eventually.of_forall fun n z _ => ?_)).congr_right
      fun z _ => ?_
    · simp only [Pi.add_apply, remainder]; ring
    · simp only [Pi.add_apply, remainder]; ring
  have hremd : ∀ n, DifferentiableOn ℂ (remainder (F n)) (ball 0 δ) := fun n =>
    differentiableOn_remainder hδ (hFd n) (hF0 n) (hFc n) (hFi n)
  have := (tendstoUniformlyOn_dslope hρ' (hρ'ρ.trans_lt hρδ) hremd
    (differentiableOn_remainder hδ hF₀d hF₀0 hF₀c hF₀i) hrem).tendsto_at
    (mem_closedBall_self hρ'.le)
  simpa only [dslope_same] using this

end Coefficients

/-! ### The kernel theorem for hulls: maps, derivatives, capacities -/

section HullKernelForward

open MapOutConstruction

variable {A : ℕ → Set ℂ} {B : Set ℂ} {R : ℝ}

theorem mapOut_eq_affine (R : ℝ) (F : ℂ → ℂ) (z : ℂ) :
    mapOut R F z = (-deriv F 0) * (F (dblι R z) + (F (dblι R z))⁻¹) +
      (((2 * R : ℝ) : ℂ) - quot F 0) := by
  simp only [mapOut, joukowski]
  ring

/-- **The coefficients of the explicit mapping-out functions converge** along a kernel-convergent
sequence of hulls in a common disc `B(0, R)`. -/
theorem tendsto_coeffs_dblRiemann {w₀ : ℂ} {F : ℕ → ℂ → ℂ} {F₀ : ℂ → ℂ}
    (hA : ∀ n, IsHPHull (A n)) (hB : IsHPHull B) (hR : 0 < R) (hAR : ∀ n, A n ⊆ ball 0 R)
    (hBR : B ⊆ ball 0 R) (hker : KernelConvergesTo (fun n => H \ A n) (H \ B) w₀)
    (hF : ∀ n, IsDblRiemann (A n) R (F n)) (hF₀ : IsDblRiemann B R F₀) :
    Tendsto (fun n => deriv (F n) 0) atTop (𝓝 (deriv F₀ 0)) ∧
      Tendsto (fun n => quot (F n) 0) atTop (𝓝 (quot F₀ 0)) ∧
      Tendsto (fun n => deriv (remainder (F n)) 0) atTop (𝓝 (deriv (remainder F₀) 0)) := by
  have hloc := tendstoLocallyUniformlyOn_dblRiemann hA hB hR hAR hBR hker hF hF₀
  have hΩBo := isOpen_dblΩ hB hR hBR
  set δ : ℝ := 1 / (4 * R) with hδdef
  have hδ : 0 < δ := by positivity
  have hBδ : ∀ n, ball (0 : ℂ) δ ⊆ dblΩ (A n) R := fun n => ball_subset_dblΩ hR (hAR n)
  have hB₀δ : ball (0 : ℂ) δ ⊆ dblΩ B R := ball_subset_dblΩ hR hBR
  have hcl : TendstoUniformlyOn F F₀ atTop (closedBall 0 (δ / 2)) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩBo).1 hloc _
      ((closedBall_subset_ball (half_lt_self hδ)).trans hB₀δ) (isCompact_closedBall _ _)
  obtain ⟨hd, hq, hr⟩ := tendsto_coeffs_of_tendstoUniformlyOn hδ
    (fun n => (hF n).1.1.mono (hBδ n)) (fun n => (hF n).1.2.injOn.mono (hBδ n))
    (fun n => (hF n).2.1) (fun n => (hF n).deriv_ne_zero)
    (hF₀.1.1.mono hB₀δ) (hF₀.1.2.injOn.mono hB₀δ) hF₀.2.1 hF₀.deriv_ne_zero hcl
  exact ⟨hd, hq, hr⟩

/-- **Convergence of the explicit mapping-out functions** of a kernel-convergent sequence of hulls
in a common disc `B(0, R)`, and of the derivatives at `0` of their remainders. -/
theorem tendstoLocallyUniformlyOn_mapOut {w₀ : ℂ} {F : ℕ → ℂ → ℂ} {F₀ : ℂ → ℂ}
    (hA : ∀ n, IsHPHull (A n)) (hB : IsHPHull B) (hR : 0 < R) (hAR : ∀ n, A n ⊆ ball 0 R)
    (hBR : B ⊆ ball 0 R) (hker : KernelConvergesTo (fun n => H \ A n) (H \ B) w₀)
    (hF : ∀ n, IsDblRiemann (A n) R (F n)) (hF₀ : IsDblRiemann B R F₀) :
    TendstoLocallyUniformlyOn (fun n => mapOut R (F n)) (mapOut R F₀) atTop (H \ B) ∧
      Tendsto (fun n => deriv (remainder (F n)) 0) atTop (𝓝 (deriv (remainder F₀) 0)) := by
  have hloc := tendstoLocallyUniformlyOn_dblRiemann hA hB hR hAR hBR hker hF hF₀
  have hΩBo := isOpen_dblΩ hB hR hBR
  obtain ⟨hd, hq, hr⟩ := tendsto_coeffs_dblRiemann hA hB hR hAR hBR hker hF hF₀
  refine ⟨?_, hr⟩
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hB.isOpen]
  intro K hKB hK
  have hKH : K ⊆ H := hKB.trans sdiff_subset
  have hιc : ContinuousOn (dblι R) K := dblι_continuousOn_H.mono hKH
  have hLc : IsCompact (dblι R '' K) := hK.image_of_continuousOn hιc
  have hLΩ : dblι R '' K ⊆ dblΩ B R := by
    rintro _ ⟨z, hz, rfl⟩
    exact ((bijOn_dblι hB).mapsTo (hKB hz)).1
  have hu : TendstoUniformlyOn (fun n => F n ∘ dblι R) (F₀ ∘ dblι R) atTop K :=
    (((tendstoLocallyUniformlyOn_iff_forall_isCompact hΩBo).1 hloc _ hLΩ hLc).comp
      (dblι R)).mono fun z hz => mem_image_of_mem _ hz
  have hu₀c : ContinuousOn (F₀ ∘ dblι R) K :=
    (hF₀.1.1.continuousOn.mono hLΩ).comp hιc (fun z hz => mem_image_of_mem _ hz)
  have hu₀0 : ∀ z ∈ K, (F₀ ∘ dblι R) z ≠ 0 := by
    intro z hz h
    have hzΩ : dblι R z ∈ dblΩ B R := hLΩ (mem_image_of_mem _ hz)
    have := hF₀.1.2.injOn hzΩ zero_mem_dblΩ (by rw [hF₀.2.1]; exact h)
    exact dblι_ne_zero (hKH hz) this
  obtain ⟨c, hc, hcK⟩ := exists_pos_le_norm_of_continuousOn hK hu₀c hu₀0
  have hsum : TendstoUniformlyOn (fun n z => F n (dblι R z) + (F n (dblι R z))⁻¹)
      (fun z => F₀ (dblι R z) + (F₀ (dblι R z))⁻¹) atTop K :=
    hu.add (tendstoUniformlyOn_inv hc hcK hu)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hu₀c.add (hu₀c.inv₀ hu₀0))
  have haff := tendstoUniformlyOn_const_mul_add (fun z hz => hM z hz) hsum hd.neg
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => ((2 * R : ℝ) : ℂ)) atTop _).sub hq)
  refine (haff.congr (Eventually.of_forall fun n z _ => ?_)).congr_right fun z _ => ?_
  · exact (mapOut_eq_affine R (F n) z).symm
  · exact (mapOut_eq_affine R F₀ z).symm

/-- A common radius for the hulls and the limit hull, with symmetric Riemann maps. -/
theorem exists_common_dblRiemann {R : ℝ} (hA : ∀ n, IsHPHull (A n)) (hB : IsHPHull B)
    (hAR : ∀ n, A n ⊆ ball 0 R) :
    ∃ R' : ℝ, 0 < R' ∧ (∀ n, A n ⊆ ball 0 R') ∧ B ⊆ ball 0 R' ∧
      ∃ F : ℕ → ℂ → ℂ, ∃ F₀ : ℂ → ℂ, (∀ n, IsDblRiemann (A n) R' (F n)) ∧
        IsDblRiemann B R' F₀ := by
  obtain ⟨R₁, hR₁, hBR₁⟩ := hB.exists_subset_ball
  have hR' : 0 < max R R₁ := lt_max_of_lt_right hR₁
  have hAR' : ∀ n, A n ⊆ ball 0 (max R R₁) := fun n =>
    (hAR n).trans (ball_subset_ball (le_max_left _ _))
  have hBR' : B ⊆ ball 0 (max R R₁) := hBR₁.trans (ball_subset_ball (le_max_right _ _))
  choose F hF using fun n => exists_isDblRiemann (hA n) hR' (hAR' n)
  obtain ⟨F₀, hF₀⟩ := exists_isDblRiemann hB hR' hBR'
  exact ⟨max R R₁, hR', hAR', hBR', F, F₀, hF, hF₀⟩

/-- **Kernel theorem for hulls, "kernel convergence ⇒ convergence of the maps"** (specification
p. 205: "Kernel convergence gives convergence of the hydrodynamically normalized maps `g_{K_N}` to
`g_K` in the common interior"; Pommerenke 1992, Theorem 1.8; [Law05] §3.6): if
`ℍ \ A n → ℍ \ B` in the kernel sense and the hulls `A n` lie in a common disc, then the
mapping-out functions converge locally uniformly on `ℍ \ B`. -/
theorem tendstoLocallyUniformlyOn_of_kernelConvergesTo_H {w₀ : ℂ} {g : ℕ → ℂ → ℂ}
    {g₀ : ℂ → ℂ} (hA : ∀ n, IsHPHull (A n)) (hB : IsHPHull B) (hAR : ∀ n, A n ⊆ ball 0 R)
    (hg : ∀ n, IsMapOut (A n) (g n)) (hg₀ : IsMapOut B g₀)
    (hker : KernelConvergesTo (fun n => H \ A n) (H \ B) w₀) :
    TendstoLocallyUniformlyOn g g₀ atTop (H \ B) := by
  obtain ⟨R', hR', hAR', hBR', F, F₀, hF, hF₀⟩ := exists_common_dblRiemann hA hB hAR
  have hmain := (tendstoLocallyUniformlyOn_mapOut hA hB hR' hAR' hBR' hker hF hF₀).1
  have hi := forall_exists_nhds_of_kernelConvergesTo hker (hB.H_diff_ne_singleton w₀)
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hB.isOpen] at hmain ⊢
  intro K hKB hK
  refine ((hmain K hKB hK).congr ?_).congr_right ?_
  · filter_upwards [eventually_subset_of_isCompact hi hK hKB] with n hn z hz
    exact IsMapOut.eqOn (hA n) (isMapOut_mapOut (hA n) hR' (hAR' n) (hF n)).1 (hg n) (hn hz)
  · exact fun z hz => IsMapOut.eqOn hB (isMapOut_mapOut hB hR' hBR' hF₀).1 hg₀ (hKB hz)

/-- **The derivatives converge as well** (Weierstrass), locally uniformly on `ℍ \ B`
(specification p. 489: "convergence of maps and derivatives"). -/
theorem tendstoLocallyUniformlyOn_deriv_of_kernelConvergesTo_H {w₀ : ℂ} {g : ℕ → ℂ → ℂ}
    {g₀ : ℂ → ℂ} (hA : ∀ n, IsHPHull (A n)) (hB : IsHPHull B) (hAR : ∀ n, A n ⊆ ball 0 R)
    (hg : ∀ n, IsMapOut (A n) (g n)) (hg₀ : IsMapOut B g₀)
    (hker : KernelConvergesTo (fun n => H \ A n) (H \ B) w₀) :
    TendstoLocallyUniformlyOn (fun n => deriv (g n)) (deriv g₀) atTop (H \ B) := by
  have hmain := tendstoLocallyUniformlyOn_of_kernelConvergesTo_H hA hB hAR hg hg₀ hker
  have hi := forall_exists_nhds_of_kernelConvergesTo hker (hB.H_diff_ne_singleton w₀)
  intro u hu x hx
  obtain ⟨r, hr, hrB⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hB.isOpen.mem_nhds hx)
  have hev := eventually_subset_of_isCompact hi (isCompact_closedBall x r) hrB
  have hdiff : ∀ᶠ n in atTop, DifferentiableOn ℂ (g n) (ball x r) :=
    hev.mono fun n hn => (hg n).1.1.mono (ball_subset_closedBall.trans hn)
  have hball := (hmain.mono (ball_subset_closedBall.trans hrB)).deriv hdiff isOpen_ball
  obtain ⟨t, ht, htev⟩ := hball u hu x (mem_ball_self hr)
  rw [isOpen_ball.nhdsWithin_eq (mem_ball_self hr)] at ht
  exact ⟨t, mem_nhdsWithin_of_mem_nhds ht, htev⟩

/-- **Continuity of the half-plane capacity along kernel convergence** (bounded hulls):
`hcap(A n) → hcap(B)`. The capacity is `−Re r'(0)` for the remainder `r` of the explicit
mapping-out function. -/
theorem tendsto_hcap_of_kernelConvergesTo_H {w₀ : ℂ} {A : ℕ → HPHull} {B : HPHull}
    (hAR : ∀ n, (A n).1 ⊆ ball 0 R)
    (hker : KernelConvergesTo (fun n => H \ (A n).1) (H \ B.1) w₀) :
    Tendsto (fun n => (A n).hcap) atTop (𝓝 B.hcap) := by
  obtain ⟨R', hR', hAR', hBR', F, F₀, hF, hF₀⟩ :=
    exists_common_dblRiemann (fun n => (A n).2) B.2 hAR
  have hr := (tendstoLocallyUniformlyOn_mapOut (fun n => (A n).2) B.2 hR' hAR' hBR' hker hF
    hF₀).2
  have hcapA : ∀ n, (A n).hcap = -(deriv (remainder (F n)) 0).re := fun n =>
    let h := isMapOut_mapOut (A n).2 hR' (hAR' n) (hF n)
    (A n).hcap_eq_of_tendsto h.1 h.2
  have hcapB : B.hcap = -(deriv (remainder F₀) 0).re :=
    let h := isMapOut_mapOut B.2 hR' hBR' hF₀
    B.hcap_eq_of_tendsto h.1 h.2
  simp only [hcapA, hcapB]
  exact ((Complex.continuous_re.tendsto _).comp hr).neg

end HullKernelForward

/-! ### Inverses of convergent conformal maps -/

section InverseConvergence

/-- The inverse `invFunOn g D` of a conformal bijection `D → V` is holomorphic on `V`
(QuantumZipper's `univalentOPH`), and a conformal bijection `V → D`. -/
theorem isConformalBijection_invFunOn {g : ℂ → ℂ} {D V : Set ℂ} (hDo : IsOpen D)
    (hg : IsConformalBijection g D V) : IsConformalBijection (invFunOn g D) V D := by
  set e := QuantumZipper.CA.univalentOPH hDo hg.1 hg.2.injOn with he
  have himg : g '' D = V := hg.2.image_eq
  have hsd : DifferentiableOn ℂ e.symm V := by
    have := QuantumZipper.CA.differentiableOn_univalentOPH_symm hDo hg.1 hg.2.injOn
    rwa [himg] at this
  have heq : EqOn (invFunOn g D) e.symm V := by
    intro w hw
    have hw' : w ∈ g '' D := himg.symm ▸ hw
    have h1 : e.symm w ∈ D := by
      have : w ∈ e.target := by rw [QuantumZipper.CA.univalentOPH_target]; exact hw'
      exact e.map_target this
    have h2 : g (e.symm w) = w :=
      QuantumZipper.CA.univalentOPH_apply_symm_apply hDo hg.1 hg.2.injOn hw'
    obtain ⟨z, hz, hzw⟩ := hw'
    have h3 : invFunOn g D w ∈ D := invFunOn_mem ⟨z, hz, hzw⟩
    have h4 : g (invFunOn g D w) = w := invFunOn_eq ⟨z, hz, hzw⟩
    exact hg.2.injOn h3 h1 (h4.trans h2.symm)
  exact ⟨hsd.congr heq, hg.2.symm hg.2.invOn_invFunOn.symm⟩

/-- **Inverses of locally uniformly convergent conformal maps converge** (Hurwitz's theorem): let
`g n` map `G n` conformally onto `V`, `g₀` map `D` conformally onto `V`, let every point of `D`
have a neighbourhood contained in all late `G n`, and `g n → g₀` locally uniformly on `D`. Then
`(g n)⁻¹ → g₀⁻¹` locally uniformly on `V`. -/
theorem tendstoLocallyUniformlyOn_invFunOn {D V : Set ℂ} {G : ℕ → Set ℂ} {g : ℕ → ℂ → ℂ}
    {g₀ : ℂ → ℂ} (hDo : IsOpen D) (hVo : IsOpen V)
    (hg : ∀ n, IsConformalBijection (g n) (G n) V) (hg₀ : IsConformalBijection g₀ D V)
    (hi : ∀ w ∈ D, ∃ U ∈ 𝓝 w, ∀ᶠ n in atTop, U ⊆ G n)
    (hlim : TendstoLocallyUniformlyOn g g₀ atTop D) :
    TendstoLocallyUniformlyOn (fun n => invFunOn (g n) (G n)) (invFunOn g₀ D) atTop V := by
  set h₀ := invFunOn g₀ D with hh₀
  have hb₀ := isConformalBijection_invFunOn hDo hg₀
  have hh₀c : ContinuousOn h₀ V := hb₀.1.continuousOn
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hVo]
  intro L hLV hL
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_contra hcon
  rw [not_eventually] at hcon
  obtain ⟨φ, hφ, hφP⟩ := extraction_of_frequently_atTop hcon
  have hex : ∀ k, ∃ w ∈ L, ε ≤ dist (h₀ w) (invFunOn (g (φ k)) (G (φ k)) w) := by
    intro k
    have := hφP k
    push Not at this
    exact this
  choose w hwL hwd using hex
  obtain ⟨w', hw'L, ψ, hψ, hψt⟩ := hL.tendsto_subseq hwL
  set z' := h₀ w' with hz'
  have hz'D : z' ∈ D := hb₀.2.mapsTo (hLV hw'L)
  have hgz' : g₀ z' = w' := hg₀.2.invOn_invFunOn.2 (hLV hw'L)
  obtain ⟨U, hU, hUev⟩ := hi z' hz'D
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.1 (inter_mem hU (hDo.mem_nhds hz'D))
  have hev1 : ∀ᶠ j in atTop, ball z' r ⊆ G (φ (ψ j)) :=
    (hφ.comp hψ).tendsto_atTop.eventually (hUev.mono fun n hn =>
      (hrsub.trans inter_subset_left).trans hn)
  obtain ⟨J, hJ⟩ := hev1.exists_forall_of_atTop
  set m : ℕ → ℕ := fun j => φ (ψ (j + J)) with hm
  have hmono : StrictMono m := (hφ.comp hψ).comp (strictMono_id.add_const J)
  have hwt : Tendsto (fun j => w (ψ (j + J))) atTop (𝓝 w') :=
    hψt.comp (tendsto_add_atTop_nat J)
  set Fj : ℕ → ℂ → ℂ := fun j z => g (m j) z - w (ψ (j + J)) with hFj
  have hFd : ∀ j, DifferentiableOn ℂ (Fj j) (ball z' r) := fun j =>
    ((hg (m j)).1.mono (hJ (j + J) (Nat.le_add_left J j))).sub_const _
  have hFlim : TendstoLocallyUniformlyOn Fj (fun z => g₀ z - w') atTop (ball z' r) :=
    QuantumZipper.CA.Kernel.tendstoLocallyUniformlyOn_sub_const
      (QuantumZipper.CA.Kernel.tendstoLocallyUniformlyOn_subseq_qz
        (hlim.mono (hrsub.trans inter_subset_right)) hmono) hwt
  have hnc : ¬ ∃ c, EqOn (fun z => g₀ z - w') (fun _ => c) (ball z' r) := by
    rintro ⟨c, hc⟩
    have hz1 : z' + (r / 2 : ℝ) ∈ ball z' r := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_real, Real.norm_eq_abs,
        abs_of_pos (half_pos hr)]
      exact half_lt_self hr
    have h1 := hc hz1
    have h2 := hc (mem_ball_self hr)
    simp only at h1 h2
    have h3 : g₀ (z' + (r / 2 : ℝ)) = g₀ z' := by linear_combination h1 - h2
    have h4 := hg₀.2.injOn (hrsub hz1).2 hz'D h3
    have : ((r / 2 : ℝ) : ℂ) = 0 := by linear_combination h4
    have : r / 2 = 0 := by exact_mod_cast this
    linarith
  have hz0 : g₀ z' - w' = 0 := by rw [hgz', sub_self]
  have hH := QuantumZipper.CA.hurwitz_eventually_exists_zero isOpen_ball
    (convex_ball z' r).isPreconnected hFd hFlim hnc (mem_ball_self hr) hz0
    (by positivity : 0 < ε / 4)
  have hc' : Tendsto (fun j => h₀ (w (ψ (j + J)))) atTop (𝓝 z') :=
    ((hh₀c.continuousAt (hVo.mem_nhds (hLV hw'L))).tendsto).comp hwt
  obtain ⟨j, ⟨z, hzB, hzε, hz0⟩, hjc⟩ :=
    (hH.and (hc'.eventually (ball_mem_nhds z' (by positivity : 0 < ε / 4)))).exists
  have hzG : z ∈ G (m j) := hJ (j + J) (Nat.le_add_left J j) hzB
  have hgz : g (m j) z = w (ψ (j + J)) := sub_eq_zero.1 hz0
  have hinvz : invFunOn (g (m j)) (G (m j)) (w (ψ (j + J))) = z := by
    rw [← hgz]
    exact (hg (m j)).2.injOn.leftInvOn_invFunOn hzG
  have hd := hwd (ψ (j + J))
  rw [hinvz] at hd
  simp only [mem_ball] at hzε hjc
  have : dist (h₀ (w (ψ (j + J)))) z ≤ dist (h₀ (w (ψ (j + J)))) z' + dist z' z :=
    dist_triangle _ _ _
  rw [dist_comm z' z] at this
  linarith

end InverseConvergence

/-! ### The kernel theorem for hulls: inverse maps and the converse -/

section HullKernelIff

variable {A : ℕ → Set ℂ} {B : Set ℂ} {R : ℝ} {g : ℕ → ℂ → ℂ} {g₀ : ℂ → ℂ}

/-- **The inverse maps `ℍ → ℍ \ A n` converge** locally uniformly on `ℍ` (bounded hulls,
kernel convergence). -/
theorem tendstoLocallyUniformlyOn_invFunOn_of_kernelConvergesTo_H {w₀ : ℂ}
    (hA : ∀ n, IsHPHull (A n)) (hB : IsHPHull B) (hAR : ∀ n, A n ⊆ ball 0 R)
    (hg : ∀ n, IsMapOut (A n) (g n)) (hg₀ : IsMapOut B g₀)
    (hker : KernelConvergesTo (fun n => H \ A n) (H \ B) w₀) :
    TendstoLocallyUniformlyOn (fun n => invFunOn (g n) (H \ A n)) (invFunOn g₀ (H \ B))
      atTop H :=
  tendstoLocallyUniformlyOn_invFunOn hB.isOpen QuantumZipper.isOpen_H (fun n => (hg n).1) hg₀.1
    (forall_exists_nhds_of_kernelConvergesTo hker (hB.H_diff_ne_singleton w₀))
    (tendstoLocallyUniformlyOn_of_kernelConvergesTo_H hA hB hAR hg hg₀ hker)

/-- **Kernel theorem for hulls, "convergence of the inverse maps ⇒ kernel convergence"**
(Pommerenke 1992, Theorem 1.8, through a disc chart of `ℍ`; no boundedness needed): if the inverse
maps `ℍ → ℍ \ A n` converge locally uniformly on `ℍ` to the inverse map of `B`, then
`ℍ \ A n → ℍ \ B` with respect to every point of `ℍ \ B`. -/
theorem kernelConvergesTo_H_of_tendstoLocallyUniformlyOn_invFunOn {w₀ : ℂ}
    (hA : ∀ n, IsHPHull (A n)) (hB : IsHPHull B) (hg : ∀ n, IsMapOut (A n) (g n))
    (hg₀ : IsMapOut B g₀) (hw₀ : w₀ ∈ H \ B)
    (hlim : TendstoLocallyUniformlyOn (fun n => invFunOn (g n) (H \ A n))
      (invFunOn g₀ (H \ B)) atTop H) :
    KernelConvergesTo (fun n => H \ A n) (H \ B) w₀ := by
  set c := g₀ w₀ with hc
  have hcH : c ∈ H := hg₀.1.2.mapsTo hw₀
  have hχ := isConformalBijection_diskChartH hcH
  have hinv : ∀ n, IsConformalBijection (invFunOn (g n) (H \ A n)) H (H \ A n) := fun n =>
    isConformalBijection_invFunOn (hA n).isOpen (hg n).1
  have hinv₀ : IsConformalBijection (invFunOn g₀ (H \ B)) H (H \ B) :=
    isConformalBijection_invFunOn hB.isOpen hg₀.1
  have h0 : (invFunOn g₀ (H \ B) ∘ diskChartH c) 0 = w₀ := by
    simp only [Function.comp_apply, diskChartH_zero, hc]
    exact hg₀.1.2.injOn.leftInvOn_invFunOn hw₀
  exact kernelConvergesTo_of_tendstoLocallyUniformlyOn
    (fun n => isConformalBijection_comp (hinv n) hχ) (isConformalBijection_comp hinv₀ hχ) h0
    (hlim.comp (diskChartH c) hχ.2.mapsTo hχ.1.continuousOn)

/-- **Kernel theorem for hulls, "convergence of the maps ⇒ kernel convergence"**: if every point of
`ℍ \ B` has a neighbourhood in all late `ℍ \ A n` and `g_{A n} → g_B` locally uniformly on
`ℍ \ B`, then `ℍ \ A n → ℍ \ B` (specification p. 357, Aux. 108: "The Loewner ODE gives kernel
convergence"). -/
theorem kernelConvergesTo_H_of_tendstoLocallyUniformlyOn {w₀ : ℂ} (hA : ∀ n, IsHPHull (A n))
    (hB : IsHPHull B) (hg : ∀ n, IsMapOut (A n) (g n)) (hg₀ : IsMapOut B g₀)
    (hw₀ : w₀ ∈ H \ B) (hi : ∀ w ∈ H \ B, ∃ U ∈ 𝓝 w, ∀ᶠ n in atTop, U ⊆ H \ A n)
    (hlim : TendstoLocallyUniformlyOn g g₀ atTop (H \ B)) :
    KernelConvergesTo (fun n => H \ A n) (H \ B) w₀ :=
  kernelConvergesTo_H_of_tendstoLocallyUniformlyOn_invFunOn hA hB hg hg₀ hw₀
    (tendstoLocallyUniformlyOn_invFunOn hB.isOpen QuantumZipper.isOpen_H (fun n => (hg n).1)
      hg₀.1 hi hlim)

/-- **Carathéodory's kernel theorem for compact `ℍ`-hulls, inverse maps** (Pommerenke 1992,
Theorem 1.8; [Law05] §3.6): for hulls in a common disc, `ℍ \ A n → ℍ \ B` in the kernel sense iff
the inverse mapping-out functions `ℍ → ℍ \ A n` converge locally uniformly on `ℍ` to that of
`B`. -/
theorem kernelConvergesTo_H_iff_tendstoLocallyUniformlyOn_invFunOn {w₀ : ℂ}
    (hA : ∀ n, IsHPHull (A n)) (hB : IsHPHull B) (hAR : ∀ n, A n ⊆ ball 0 R)
    (hg : ∀ n, IsMapOut (A n) (g n)) (hg₀ : IsMapOut B g₀) (hw₀ : w₀ ∈ H \ B) :
    KernelConvergesTo (fun n => H \ A n) (H \ B) w₀ ↔
      TendstoLocallyUniformlyOn (fun n => invFunOn (g n) (H \ A n)) (invFunOn g₀ (H \ B))
        atTop H :=
  ⟨tendstoLocallyUniformlyOn_invFunOn_of_kernelConvergesTo_H hA hB hAR hg hg₀,
    kernelConvergesTo_H_of_tendstoLocallyUniformlyOn_invFunOn hA hB hg hg₀ hw₀⟩

/-- **Carathéodory's kernel theorem for compact `ℍ`-hulls, mapping-out functions**: for hulls in
a common disc, `ℍ \ A n → ℍ \ B` in the kernel sense iff every point of `ℍ \ B` has a
neighbourhood in all late `ℍ \ A n` and `g_{A n} → g_B` locally uniformly on `ℍ \ B`. -/
theorem kernelConvergesTo_H_iff_tendstoLocallyUniformlyOn {w₀ : ℂ} (hA : ∀ n, IsHPHull (A n))
    (hB : IsHPHull B) (hAR : ∀ n, A n ⊆ ball 0 R) (hg : ∀ n, IsMapOut (A n) (g n))
    (hg₀ : IsMapOut B g₀) (hw₀ : w₀ ∈ H \ B) :
    KernelConvergesTo (fun n => H \ A n) (H \ B) w₀ ↔
      (∀ w ∈ H \ B, ∃ U ∈ 𝓝 w, ∀ᶠ n in atTop, U ⊆ H \ A n) ∧
        TendstoLocallyUniformlyOn g g₀ atTop (H \ B) :=
  ⟨fun hker => ⟨forall_exists_nhds_of_kernelConvergesTo hker (hB.H_diff_ne_singleton w₀),
      tendstoLocallyUniformlyOn_of_kernelConvergesTo_H hA hB hAR hg hg₀ hker⟩,
    fun h => kernelConvergesTo_H_of_tendstoLocallyUniformlyOn hA hB hg hg₀ hw₀ h.1 h.2⟩

/-- **Increasing hulls** (specification p. 205: "The domains `ℍ \ K_N` decrease in the kernel
sense to `ℍ \ K`"): if `A n` increase with union `B`, then `ℍ \ A n → ℍ \ B` with respect to every
point of `ℍ \ B`. -/
theorem kernelConvergesTo_H_of_monotone {w₀ : ℂ} (hmono : Monotone A) (hA : ∀ n, IsHPHull (A n))
    (hB : IsHPHull B) (hU : ⋃ n, A n = B) (hw₀ : w₀ ∈ H \ B) :
    KernelConvergesTo (fun n => H \ A n) (H \ B) w₀ := by
  have hI : ⋂ n, H \ A n = H \ B := by
    rw [← hU]
    ext z
    simp only [mem_iInter, Set.mem_sdiff, mem_iUnion, not_exists]
    exact ⟨fun h => ⟨(h 0).1, fun n => (h n).2⟩, fun h n => ⟨h.1, h.2 n⟩⟩
  have hker := kernelConvergesTo_connectedComponentIn_of_antitone
    (G := fun n => H \ A n) (w₀ := w₀) (fun m n hmn => sdiff_subset_sdiff_right (hmono hmn))
    (fun n => (hA n).isOpen)
    (fun h => by
      have : (-I : ℂ) ∈ H \ A 0 := h ▸ mem_univ _
      have h1 : (0 : ℝ) < (-I : ℂ).im := this.1
      simp only [neg_im, I_im] at h1
      linarith)
    (by rw [hI, hB.isOpen.interior_eq]; exact hw₀)
  rwa [hI, hB.isOpen.interior_eq, hB.isConnected.isPreconnected.connectedComponentIn hw₀] at hker

/-- **Decreasing hulls** (specification p. 489: a hull "approximated from outside"): if `A n`
decrease with intersection `B`, then `ℍ \ A n → ℍ \ B` with respect to every point of `ℍ \ B`. -/
theorem kernelConvergesTo_H_of_antitone {w₀ : ℂ} (hanti : Antitone A) (hA : ∀ n, IsHPHull (A n))
    (hB : IsHPHull B) (hI : ⋂ n, A n = B) (hw₀ : w₀ ∈ H \ B) :
    KernelConvergesTo (fun n => H \ A n) (H \ B) w₀ := by
  have hU : ⋃ n, H \ A n = H \ B := by
    rw [← hI]
    ext z
    simp only [mem_iUnion, Set.mem_sdiff, mem_iInter, not_forall]
    exact ⟨fun ⟨n, h1, h2⟩ => ⟨h1, n, h2⟩, fun ⟨h1, n, h2⟩ => ⟨n, h1, h2⟩⟩
  obtain ⟨R₀, hR₀, hA0⟩ := (hA 0).exists_subset_ball
  have hw₁ : (R₀ : ℂ) * I ∈ H \ A 0 := by
    refine ⟨show 0 < ((R₀ : ℂ) * I).im by simpa using hR₀, fun h => ?_⟩
    have := mem_ball_zero_iff.1 (hA0 h)
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hR₀] at this
    exact lt_irrefl _ this
  have hker := kernelConvergesTo_iUnion_of_monotone (G := fun n => H \ A n)
    (fun m n hmn => sdiff_subset_sdiff_right (hanti hmn)) (fun n => (hA n).isOpen)
    (fun n => (hA n).isConnected.isPreconnected) hw₁
    (by
      rw [hU]
      intro h
      have : (-I : ℂ) ∈ H \ B := h ▸ mem_univ _
      have h1 : (0 : ℝ) < (-I : ℂ).im := this.1
      simp only [neg_im, I_im] at h1
      linarith)
  rw [hU] at hker
  exact kernelConvergesTo_of_mem hker (hB.H_diff_ne_singleton _) hw₀

end HullKernelIff

/-! ### Untouched real collars: a uniform growth bound -/

section Growth

open MapOutConstruction

variable {A : ℕ → Set ℂ} {B : Set ℂ} {R : ℝ} {g : ℕ → ℂ → ℂ}

theorem exists_norm_le_of_tendsto {u : ℕ → ℂ} {x : ℂ} (hu : Tendsto u atTop (𝓝 x)) :
    ∃ C, 0 ≤ C ∧ ∀ n, ‖u n‖ ≤ C := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (isBounded_range_of_tendsto u hu)
  exact ⟨C, (norm_nonneg _).trans (hC _ (mem_range_self 0)), fun n => hC _ (mem_range_self n)⟩

/-- **Uniform growth bound for the mapping-out functions** of a kernel-convergent sequence of
bounded hulls: `‖g_{A n}(z)‖ ≤ C₁ + C₂ ‖2R' − z‖` on `ℍ \ A n`, with constants independent of `n`
(doubling formula `g = −F'(0)(u + 1/u) + c`, `u = F(ι z)`, and Koebe's growth theorem for the
inverse maps, which bounds `1/‖u‖` by a multiple of `1/‖ι z‖ = ‖2R' − z‖`). -/
theorem exists_norm_le_of_kernelConvergesTo_H {w₀ : ℂ} (hA : ∀ n, IsHPHull (A n))
    (hB : IsHPHull B) (hAR : ∀ n, A n ⊆ ball 0 R) (hg : ∀ n, IsMapOut (A n) (g n))
    (hker : KernelConvergesTo (fun n => H \ A n) (H \ B) w₀) :
    ∃ R' C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      ∀ n, ∀ z ∈ H \ A n, ‖g n z‖ ≤ C₁ + C₂ * ‖((2 * R' : ℝ) : ℂ) - z‖ := by
  obtain ⟨R', hR', hAR', hBR', F, F₀, hF, hF₀⟩ := exists_common_dblRiemann hA hB hAR
  have hkΩ := kernelConvergesTo_dblΩ hA hB hR' hAR' hBR' hker
  have hΩo : ∀ n, IsOpen (dblΩ (A n) R') := fun n => isOpen_dblΩ (hA n) hR' (hAR' n)
  have hinv := fun n => isConformalBijection_invFunOn_ball (hΩo n) (hF n).1 zero_mem_dblΩ
    (hF n).2.1 (hF n).deriv_pos
  have hinv₀ := isConformalBijection_invFunOn_ball (isOpen_dblΩ hB hR' hBR') hF₀.1
    zero_mem_dblΩ hF₀.2.1 hF₀.deriv_pos
  have hlim := (kernel_convergence_iff (fun n => (hinv n).1) (fun n => (hinv n).2.1)
    (fun n => (hinv n).2.2) (Or.inr hinv₀)).2 hkΩ
  obtain ⟨P, hP0, hP⟩ := exists_norm_le_of_tendsto
    (tendsto_deriv_of_tendstoLocallyUniformlyOn (fun n => (hinv n).1.1) hlim
      (mem_ball_self one_pos))
  obtain ⟨hd, hq, -⟩ := tendsto_coeffs_dblRiemann hA hB hR' hAR' hBR' hker hF hF₀
  obtain ⟨Q, hQ0, hQ⟩ := exists_norm_le_of_tendsto hd
  obtain ⟨S, hS0, hS⟩ := exists_norm_le_of_tendsto
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => ((2 * R' : ℝ) : ℂ)) atTop _).sub hq)
  set κ := QuantumZipper.CA.Koebe.koebeDistExp with hκ
  have hκpos : 0 < κ := QuantumZipper.CA.Koebe.koebeDistExp_pos
  set K := P * (1 / 2 : ℝ) ^ (-κ) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨R', Q * 3 + S, Q * K, by positivity, by positivity, fun n z hz => ?_⟩
  have hgz : g n z = mapOut R' (F n) z :=
    (IsMapOut.eqOn (hA n) (isMapOut_mapOut (hA n) hR' (hAR' n) (hF n)).1 (hg n) hz).symm
  rw [hgz, mapOut_eq_affine]
  set w := ((2 * R' : ℝ) : ℂ) - z with hw
  have hwpos : 0 < ‖w‖ := by
    refine norm_pos_iff.2 fun h => ?_
    have := congrArg Complex.im h
    have hz' : 0 < z.im := hz.1
    simp [hw] at this
    linarith
  set ζ := dblι R' z with hζ
  have hζΩ : ζ ∈ dblΩ (A n) R' := ((bijOn_dblι (hA n)).mapsTo hz).1
  have hζ0 : ζ ≠ 0 := dblι_ne_zero hz.1
  set u := F n ζ with hu
  have hu1 : u ∈ ball (0 : ℂ) 1 := (hF n).1.2.mapsTo hζΩ
  have hu0 : u ≠ 0 := fun h =>
    hζ0 ((hF n).1.2.injOn hζΩ zero_mem_dblΩ (by rw [(hF n).2.1]; exact h))
  have hupos : 0 < ‖u‖ := norm_pos_iff.2 hu0
  have hun1 : ‖u‖ < 1 := mem_ball_zero_iff.1 hu1
  have hφu : invFunOn (F n) (dblΩ (A n) R') u = ζ := (hF n).1.2.injOn.leftInvOn_invFunOn hζΩ
  have hinvu : ‖u⁻¹‖ ≤ 2 + K * ‖w‖ := by
    rw [norm_inv]
    by_cases hu2 : (1 / 2 : ℝ) ≤ ‖u‖
    · have : ‖u‖⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ hupos two_pos]
        linarith
      have : 0 ≤ K * ‖w‖ := by positivity
      linarith
    · push Not at hu2
      have hgrowth := QuantumZipper.CA.Koebe.norm_sub_le_growth_global (hinv n).1.1
        (hinv n).1.2.injOn hu1
      rw [hφu, (hinv n).2.1, sub_zero, dist_zero_right, div_one] at hgrowth
      have hpow : (1 - ‖u‖) ^ (-κ) ≤ (1 / 2 : ℝ) ^ (-κ) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) (by linarith) (by linarith)
      have hζn : ‖ζ‖ = ‖w‖⁻¹ := by rw [hζ, dblι, norm_inv]
      have h1 : ‖w‖⁻¹ ≤ ‖u‖ * K := by
        rw [← hζn]
        refine hgrowth.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
        exact mul_le_mul (hP n) hpow (by positivity) hP0
      have h2 : 1 ≤ ‖u‖ * (K * ‖w‖) := by
        have := mul_le_mul_of_nonneg_right h1 hwpos.le
        rw [inv_mul_cancel₀ hwpos.ne'] at this
        linarith [this, show ‖u‖ * K * ‖w‖ = ‖u‖ * (K * ‖w‖) by ring]
      have h3 : ‖u‖⁻¹ ≤ K * ‖w‖ :=
        calc ‖u‖⁻¹ = ‖u‖⁻¹ * 1 := (mul_one _).symm
          _ ≤ ‖u‖⁻¹ * (‖u‖ * (K * ‖w‖)) :=
              mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 (norm_nonneg _))
          _ = K * ‖w‖ := by field_simp
      linarith
  calc ‖-deriv (F n) 0 * (u + u⁻¹) + (((2 * R' : ℝ) : ℂ) - quot (F n) 0)‖
      ≤ ‖deriv (F n) 0‖ * (‖u‖ + ‖u⁻¹‖) + ‖((2 * R' : ℝ) : ℂ) - quot (F n) 0‖ := by
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        rw [norm_mul, norm_neg]
        exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
    _ ≤ Q * (1 + (2 + K * ‖w‖)) + S :=
        add_le_add (mul_le_mul (hQ n) (add_le_add hun1.le hinvu) (by positivity) hQ0) (hS n)
    _ = Q * 3 + S + Q * K * ‖w‖ := by ring

end Growth

/-! ### Untouched real collars: reflected convergence -/

section Collar

/-- Vertical approach to a point of a disc centred on `ℝ`, from inside the upper half-disc. -/
theorem tendsto_add_mul_I_nhdsWithin {y s : ℝ} {x : ℂ} (hx : x ∈ ball (y : ℂ) s)
    (hx0 : x.im = 0) :
    Tendsto (fun t : ℝ => x + t * I) (𝓝[>] 0) (𝓝[ball (y : ℂ) s ∩ H] x) := by
  have hc : Tendsto (fun t : ℝ => x + t * I) (𝓝 0) (𝓝 x) := by
    have : Continuous (fun t : ℝ => x + t * I) := by fun_prop
    simpa using this.tendsto 0
  refine tendsto_nhdsWithin_iff.2 ⟨hc.mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [(hc.mono_left nhdsWithin_le_nhds).eventually (isOpen_ball.mem_nhds hx),
    self_mem_nhdsWithin] with t ht htpos
  refine ⟨ht, show 0 < (x + t * I).im from ?_⟩
  simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero, hx0,
    zero_add]
  exact htpos

theorem conj_mem_ball_ofReal' {y s : ℝ} {z : ℂ} (hz : z ∈ ball (y : ℂ) s) :
    conj z ∈ ball (y : ℂ) s := by
  rw [mem_ball, ← conj_ofReal, dist_conj_conj]
  exact hz

/-- **A holomorphic extension of a mapping-out function across an untouched real disc commutes
with `conj`**: it is real on the real diameter (`Im g → 0` at the boundary), hence equal to its
reflection (identity theorem). -/
theorem IsMapOut.extension_conj {E : Set ℂ} {g G : ℂ → ℂ} (hE : IsHPHull E) (hg : IsMapOut E g)
    {y s : ℝ} (hd : Disjoint (ball (y : ℂ) s) E) (hG : DifferentiableOn ℂ G (ball (y : ℂ) s))
    (hGg : EqOn G g (ball (y : ℂ) s ∩ H)) :
    ∀ z ∈ ball (y : ℂ) s, G (conj z) = conj (G z) := by
  intro z hz
  have hs : 0 < s := pos_of_mem_ball hz
  have hSE : ball (y : ℂ) s ∩ H ⊆ H \ E := fun w hw => ⟨hw.2, disjoint_left.1 hd hw.1⟩
  -- realness on the diameter
  have hreal : ∀ x ∈ ball (y : ℂ) s, x.im = 0 → (G x).im = 0 := by
    intro x hx hx0
    have ht := tendsto_add_mul_I_nhdsWithin hx hx0
    have h1 : Tendsto (fun t : ℝ => (G (x + t * I)).im) (𝓝[>] 0) (𝓝 (G x).im) :=
      (continuous_im.tendsto _).comp ((hG.continuousOn.continuousAt
        (isOpen_ball.mem_nhds hx)).tendsto.comp (ht.mono_right nhdsWithin_le_nhds))
    have hq : x ∉ H \ E := fun h => by
      have : (0 : ℝ) < x.im := h.1
      linarith
    have h2 : Tendsto (fun t : ℝ => (G (x + t * I)).im) (𝓝[>] 0) (𝓝 0) := by
      have := (hg.tendsto_im_nhdsWithin hE hq).comp
        (ht.mono_right (nhdsWithin_mono _ hSE))
      refine this.congr' ?_
      filter_upwards [ht.eventually self_mem_nhdsWithin] with t htS
      simp only [Function.comp_apply, hGg htS]
    exact tendsto_nhds_unique h1 h2
  -- the reflection agrees with `G`
  set Gc : ℂ → ℂ := fun w => conj (G (conj w)) with hGc
  have hGcd : DifferentiableOn ℂ Gc (ball (y : ℂ) s) := by
    intro w hw
    have hcw := conj_mem_ball_ofReal' hw
    have hd' : DifferentiableAt ℂ G (conj w) := hG.differentiableAt (isOpen_ball.mem_nhds hcw)
    exact (differentiableAt_conj_conj_iff.2 hd').differentiableWithinAt
  have hfreq : ∃ᶠ w in 𝓝[≠] (y : ℂ), G w = Gc w := by
    have htend : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] y) (𝓝[≠] (y : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨(continuous_ofReal.tendsto y).mono_left nhdsWithin_le_nhds,
        eventually_nhdsWithin_of_forall fun t ht => ?_⟩
      simpa using ht
    refine htend.frequently (Eventually.frequently ?_)
    filter_upwards [(continuous_ofReal.tendsto y).mono_left nhdsWithin_le_nhds
      |>.eventually (isOpen_ball.mem_nhds (mem_ball_self hs))] with t ht
    have h1 := hreal _ ht (ofReal_im t)
    simp only [hGc, conj_ofReal]
    exact (Complex.conj_eq_iff_im.2 h1).symm
  have heq := (hG.analyticOnNhd isOpen_ball).eqOn_of_preconnected_of_frequently_eq
    (hGcd.analyticOnNhd isOpen_ball) (convex_ball _ _).isPreconnected (mem_ball_self hs) hfreq
  have := heq (conj_mem_ball_ofReal' hz)
  simp only [hGc, conj_conj] at this
  exact this

/-- **A bound for the extension** from a bound on the upper half-disc. -/
theorem IsMapOut.norm_extension_le {E : Set ℂ} {g G : ℂ → ℂ} (hE : IsHPHull E)
    (hg : IsMapOut E g) {y s : ℝ} (hd : Disjoint (ball (y : ℂ) s) E)
    (hG : DifferentiableOn ℂ G (ball (y : ℂ) s)) (hGg : EqOn G g (ball (y : ℂ) s ∩ H)) {M : ℝ}
    (hM : ∀ z ∈ ball (y : ℂ) s ∩ H, ‖g z‖ ≤ M) : ∀ z ∈ ball (y : ℂ) s, ‖G z‖ ≤ M := by
  have hup : ∀ z ∈ ball (y : ℂ) s ∩ H, ‖G z‖ ≤ M := fun z hz => by rw [hGg hz]; exact hM z hz
  intro z hz
  rcases lt_trichotomy z.im 0 with h | h | h
  · have hcz : conj z ∈ ball (y : ℂ) s ∩ H :=
      ⟨conj_mem_ball_ofReal' hz, show 0 < (conj z).im by simp; linarith⟩
    have := IsMapOut.extension_conj hE hg hd hG hGg (conj z) hcz.1
    rw [conj_conj] at this
    rw [this, Complex.norm_conj]
    exact hup _ hcz
  · have ht := tendsto_add_mul_I_nhdsWithin hz h
    have h1 : Tendsto (fun t : ℝ => ‖G (z + t * I)‖) (𝓝[>] 0) (𝓝 ‖G z‖) :=
      (continuous_norm.tendsto _).comp ((hG.continuousOn.continuousAt
        (isOpen_ball.mem_nhds hz)).tendsto.comp (ht.mono_right nhdsWithin_le_nhds))
    refine le_of_tendsto h1 ?_
    filter_upwards [ht.eventually self_mem_nhdsWithin] with t htS
    exact hup _ htS
  · exact hup z ⟨hz, h⟩

variable {A : ℕ → Set ℂ} {B : Set ℂ} {R : ℝ} {g : ℕ → ℂ → ℂ} {g₀ : ℂ → ℂ}

/-- **Reflected convergence on an untouched real collar** (specification p. 205: "Reflection
across a slightly larger untouched interval gives locally uniform convergence there as well, and
hence convergence of the derivatives"; p. 489: "Kernel convergence and reflection on a fixed
untouched collar give convergence of maps and derivatives there"). Let `ℍ \ A n → ℍ \ B` with all
hulls in a common disc, let the disc `B(y, s)`, `y ∈ ℝ`, avoid every `A n` and `B`, and let `G n`,
`G₀` be holomorphic on `B(y, s)` and extend `g_{A n}`, `g_B` (such extensions exist by Schwarz
reflection). Then `G n → G₀` and `G n' → G₀'` locally uniformly on `B(y, s)`.
(The extensions are bounded uniformly by `exists_norm_le_of_kernelConvergesTo_H` and their
conj-symmetry; Montel's theorem and the identity theorem identify every subsequential limit.) -/
theorem tendstoLocallyUniformlyOn_extension_of_kernelConvergesTo_H {w₀ : ℂ}
    (hA : ∀ n, IsHPHull (A n)) (hB : IsHPHull B) (hAR : ∀ n, A n ⊆ ball 0 R)
    (hg : ∀ n, IsMapOut (A n) (g n)) (hg₀ : IsMapOut B g₀)
    (hker : KernelConvergesTo (fun n => H \ A n) (H \ B) w₀) {y s : ℝ}
    (hdA : ∀ n, Disjoint (ball (y : ℂ) s) (A n)) (hdB : Disjoint (ball (y : ℂ) s) B)
    {G : ℕ → ℂ → ℂ} {G₀ : ℂ → ℂ} (hG : ∀ n, DifferentiableOn ℂ (G n) (ball (y : ℂ) s))
    (hGg : ∀ n, EqOn (G n) (g n) (ball (y : ℂ) s ∩ H))
    (hG₀ : DifferentiableOn ℂ G₀ (ball (y : ℂ) s)) (hG₀g : EqOn G₀ g₀ (ball (y : ℂ) s ∩ H)) :
    TendstoLocallyUniformlyOn G G₀ atTop (ball (y : ℂ) s) ∧
      TendstoLocallyUniformlyOn (fun n => deriv (G n)) (deriv G₀) atTop (ball (y : ℂ) s) := by
  have hconv : TendstoLocallyUniformlyOn G G₀ atTop (ball (y : ℂ) s) := by
    obtain ⟨R', C₁, C₂, hC₁, hC₂, hC⟩ := exists_norm_le_of_kernelConvergesTo_H hA hB hAR hg hker
    set M := C₁ + C₂ * (|2 * R'| + (|y| + |s|)) with hM
    have hbd : ∀ n, ∀ z ∈ ball (y : ℂ) s, ‖G n z‖ ≤ M := by
      intro n
      refine IsMapOut.norm_extension_le (hA n) (hg n) (hdA n) (hG n) (hGg n) fun z hz => ?_
      refine (hC n z ⟨hz.2, disjoint_left.1 (hdA n) hz.1⟩).trans ?_
      rw [hM]
      refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hC₂)
      have h1 : ‖z‖ ≤ |y| + |s| := by
        have := mem_ball.1 hz.1
        rw [dist_eq_norm] at this
        have h2 : ‖z‖ ≤ ‖z - (y : ℂ)‖ + ‖(y : ℂ)‖ := by
          calc ‖z‖ = ‖(z - (y : ℂ)) + (y : ℂ)‖ := by ring_nf
            _ ≤ _ := norm_add_le _ _
        rw [Complex.norm_real, Real.norm_eq_abs] at h2
        linarith [le_abs_self s]
      calc ‖((2 * R' : ℝ) : ℂ) - z‖ ≤ ‖((2 * R' : ℝ) : ℂ)‖ + ‖z‖ := norm_sub_le _ _
        _ ≤ |2 * R'| + (|y| + |s|) := by
            rw [Complex.norm_real, Real.norm_eq_abs]; linarith
    have hmain := tendstoLocallyUniformlyOn_of_kernelConvergesTo_H hA hB hAR hg hg₀ hker
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball]
    intro K hKB hK
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    by_contra hcon
    rw [not_eventually] at hcon
    obtain ⟨φ, hφ, hφP⟩ := extraction_of_frequently_atTop hcon
    obtain ⟨ψ, f, hψ, hfd, hflim⟩ := QuantumZipper.CA.montel isOpen_ball (fun k => hG (φ k))
      fun K' hK'B _ => ⟨M, fun k z hz => hbd _ z (hK'B hz)⟩
    have hup : EqOn f G₀ (ball (y : ℂ) s ∩ H) := by
      intro z hz
      have hzB : z ∈ H \ B := ⟨hz.2, disjoint_left.1 hdB hz.1⟩
      have h1 : Tendsto (fun k => G (φ (ψ k)) z) atTop (𝓝 (f z)) := hflim.tendsto_at hz.1
      have h2 : Tendsto (fun k => G (φ (ψ k)) z) atTop (𝓝 (G₀ z)) := by
        rw [hG₀g hz]
        refine ((hmain.tendsto_at hzB).comp (hφ.comp hψ).tendsto_atTop).congr fun k => ?_
        exact (hGg _ hz).symm
      exact tendsto_nhds_unique h1 h2
    have hs : 0 < s := by
      by_contra hs
      obtain ⟨k, hk⟩ := (hcon.and_eventually (Eventually.of_forall fun _ => trivial)).exists
      apply hk.1
      intro x hx
      have := pos_of_mem_ball (hKB hx)
      exact absurd this hs
    set z₁ : ℂ := (y : ℂ) + ((s / 2 : ℝ) : ℂ) * I with hz₁def
    have hz₁ : z₁ ∈ ball (y : ℂ) s ∩ H := by
      refine ⟨?_, show 0 < z₁.im by simp [hz₁def]; linarith⟩
      rw [mem_ball, dist_eq_norm, hz₁def, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hs)]
      exact half_lt_self hs
    have hfeq : EqOn f G₀ (ball (y : ℂ) s) :=
      (hfd.analyticOnNhd isOpen_ball).eqOn_of_preconnected_of_eventuallyEq
        (hG₀.analyticOnNhd isOpen_ball) (convex_ball _ _).isPreconnected hz₁.1
        (Filter.eventuallyEq_of_mem ((isOpen_ball.inter QuantumZipper.isOpen_H).mem_nhds hz₁) hup)
    have hK' := ((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).1 hflim K hKB
      hK).congr_right (hfeq.mono hKB)
    rw [Metric.tendstoUniformlyOn_iff] at hK'
    obtain ⟨k, hk⟩ := (hK' ε hε).exists
    exact hφP (ψ k) hk
  exact ⟨hconv, hconv.deriv (Eventually.of_forall hG) isOpen_ball⟩

end Collar

/-! ### Monotone sequences of hulls -/

section MonotoneHulls

variable {A : ℕ → Set ℂ} {B : Set ℂ} {g : ℕ → ℂ → ℂ} {g₀ : ℂ → ℂ}

/-- **Increasing hulls** (specification p. 205): if `A n` increase with union `B`, then
`g_{A n} → g_B` locally uniformly on `ℍ \ B`. -/
theorem tendstoLocallyUniformlyOn_of_monotone_H (hmono : Monotone A) (hA : ∀ n, IsHPHull (A n))
    (hB : IsHPHull B) (hU : ⋃ n, A n = B) (hg : ∀ n, IsMapOut (A n) (g n))
    (hg₀ : IsMapOut B g₀) : TendstoLocallyUniformlyOn g g₀ atTop (H \ B) := by
  obtain ⟨R, -, hBR⟩ := hB.exists_subset_ball
  have hAR : ∀ n, A n ⊆ ball 0 R := fun n => (subset_iUnion A n).trans (hU ▸ hBR)
  obtain ⟨w₀, hw₀⟩ : (H \ B).Nonempty := hB.isConnected.nonempty
  exact tendstoLocallyUniformlyOn_of_kernelConvergesTo_H hA hB hAR hg hg₀
    (kernelConvergesTo_H_of_monotone hmono hA hB hU hw₀)

/-- **Decreasing hulls** (specification p. 489, approximation from outside): if `A n` decrease with
intersection `B`, then `g_{A n} → g_B` locally uniformly on `ℍ \ B`. -/
theorem tendstoLocallyUniformlyOn_of_antitone_H (hanti : Antitone A) (hA : ∀ n, IsHPHull (A n))
    (hB : IsHPHull B) (hI : ⋂ n, A n = B) (hg : ∀ n, IsMapOut (A n) (g n))
    (hg₀ : IsMapOut B g₀) : TendstoLocallyUniformlyOn g g₀ atTop (H \ B) := by
  obtain ⟨R, -, hA0R⟩ := (hA 0).exists_subset_ball
  have hAR : ∀ n, A n ⊆ ball 0 R := fun n => (hanti (Nat.zero_le n)).trans hA0R
  obtain ⟨w₀, hw₀⟩ : (H \ B).Nonempty := hB.isConnected.nonempty
  exact tendstoLocallyUniformlyOn_of_kernelConvergesTo_H hA hB hAR hg hg₀
    (kernelConvergesTo_H_of_antitone hanti hA hB hI hw₀)

end MonotoneHulls

end InteractingSLE
