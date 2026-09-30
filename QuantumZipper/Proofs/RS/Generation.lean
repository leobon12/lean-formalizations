import QuantumZipper.Proofs.RS.GenerationBasic
import QuantumZipper.Proofs.Loewner.CoreArc1

/-!
# EXT-RS node GEN: the trace generates the hulls (no path from the hull to the outside)

Blueprint `blueprint/EXT_RS_BLUEPRINT.md` §3, node **GEN** (task RS-GEN), deterministic.
Notation: `f_s = fwdMap W s`, `f̂_s = fwdMapInv W s`, `K_s = fwdHull W s`, `H = {0 < Im}`,
`A = trace W '' [0,t]`.

## Main result

`gen_no_path`: if `W` is continuous with `W 0 = 0`, `t ≥ 0`, the radial limits
`f̂_s(iy) → trace W s` (`y ↓ 0`) hold **uniformly** in `s ∈ [0,t]`, and `trace W` is continuous
on `[0,t]`, then no path in `H \ A` joins a point of `K_t` to a point of `H \ K_t`.

## Proof (blueprint GEN steps 1–6)

1. Replace `p` by the last point `p' = β(u₀)` of the path in `K_t` (`K_t` is relatively closed
   in `H`).
2. `d > 0` is the distance between the compact sets `range β` and `A`; `m > 0` is a lower bound
   of `Im f_s q` on `s ∈ [0,t]` (CoreArc1 `exists_im_lower_of_isCompact`).
3. Choose `ε < min(1, m)` so small that radial distances below `ε` are `< d/2` and
   `2π²R₀²/log(1/ε) < (d/2)²`, where `R₀` bounds `f̂_s` on the unit half-disk uniformly in `s`
   (`fwdMapInv_mem_H_bound`).
4. Pick `s < τ_{p'}` with `|f_s p'| < ε²` (CoreArc1 `exists_small_of_mem_fwdHull`).
5. Wolff's lemma (EXT-CA C2, `exists_short_semicircle_finite`; Pommerenke, *Boundary Behaviour
   of Conformal Maps*, Prop. 2.2, p. 20) gives `r ∈ (ε², ε)` such that every point of
   `f̂_s({|w| = r} ∩ H)` is within `d/2` of `f̂_s(ir)`, which is within `d/2` of `trace W s ∈ A`.
6. By the intermediate value theorem on `u ↦ |f_s(β u)|` over `[u₀, 1]` (from `< ε² < r` to
   `≥ m > r`) some `β u = f̂_s(w)` with `|w| = r`: then `dist(β u, A) < d`, a contradiction.

Sources: statement Rohde–Schramm, *Basic properties of SLE*, Ann. Math. 161 (2005), Thm 4.1
(p. 19); Kemppainen, *Schramm–Loewner Evolution* (2017), Thm 6.4 and Cor 6.2 (pp. 109–110);
Lawler, *Conformally Invariant Processes in the Plane* (2005), Prop 4.28 (pp. 87–88).
**Own adaptation** (blueprint §9, DEVIATIONS L-RS2 item 2): RS's proof of Thm 4.1 rests on
Pommerenke Prop. 2.14 (limits along arcs), which Pommerenke derives from Wolff's lemma
(Prop. 2.2); we inline that Wolff-lemma core instead of prime ends, accessibility or the kernel
theorem. Hypotheses: RS assume only pointwise radial limits and continuity of the trace; as in the
blueprint we assume the convergence is uniform on `[0,t]` (this is what TR3/TR4 deliver).
-/

noncomputable section

open Set Filter Topology Metric Complex MeasureTheory
open scoped ENNReal Real

namespace QuantumZipper
namespace RS

variable {W : ℝ → ℝ}

/-- **GEN, step 5 (Wolff).** If `f̂_s` is bounded by `R₀` on the unit half-disk and
`0 < ε < 1`, there is a radius `r ∈ (ε², ε)` such that every point `f̂_s w`, `w ∈ H`, `|w| = r`,
satisfies `‖f̂_s w − f̂_s(ir)‖² ≤ 2π²R₀²/log(1/ε)`. -/
theorem exists_semicircle_close (hW : Continuous W) (hW0 : W 0 = 0) {s : ℝ} (hs : 0 ≤ s)
    {R₀ : ℝ} (hR : ∀ w ∈ H, ‖w‖ < 1 → ‖fwdMapInv W s w‖ < R₀) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) :
    ∃ r ∈ Ioo (ε ^ 2) ε, ∀ w ∈ H, ‖w‖ = r →
      ‖fwdMapInv W s w - fwdMapInv W s (r * I)‖ ^ 2 ≤ 2 * π ^ 2 * R₀ ^ 2 / Real.log (1 / ε) := by
  set U : Set ℂ := {z : ℂ | 0 < z.im ∧ ‖z‖ < 1} with hUdef
  have hU : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt continuous_norm continuous_const)
  have hUH : U ⊆ H := fun z hz => hz.1
  have hg : DifferentiableOn ℂ (fwdMapInv W s) H := fun z hz =>
    (differentiableAt_fwdMapInv hW hW0 hs hz).differentiableWithinAt
  have hd : DifferentiableOn ℂ (fwdMapInv W s) U := hg.mono hUH
  have hi : InjOn (fwdMapInv W s) U := (injOn_fwdMapInv_H hW hW0 hs).mono hUH
  have hRimg : fwdMapInv W s '' U ⊆ ball 0 R₀ := by
    rintro _ ⟨z, hz, rfl⟩
    exact mem_ball_zero_iff.2 (hR z hz.1 hz.2)
  have hsub : {z : ℂ | 0 < z.im ∧ ‖z - ((0 : ℝ) : ℂ)‖ < ε} ⊆ U := fun z hz =>
    ⟨hz.1, by simpa using hz.2.trans hε1⟩
  obtain ⟨r, hr, hfin, hb⟩ :=
    CA.Car.exists_short_semicircle_finite hU hd hi hRimg hε0 hε1 hsub
  simp only [Complex.ofReal_zero, zero_add] at hfin hb
  set L := ∫⁻ θ in Ioo 0 π, ‖deriv (fwdMapInv W s) (r * exp (θ * I))‖ₑ * ENNReal.ofReal r
    with hL
  have hr0 : 0 < r := (pow_pos hε0 2).trans hr.1
  have hlog : 0 < Real.log (1 / ε) := Real.log_pos ((one_lt_div hε0).2 hε1)
  have hc0 : 0 ≤ 2 * π ^ 2 * R₀ ^ 2 / Real.log (1 / ε) := by positivity
  have hLsq : L.toReal ^ 2 ≤ 2 * π ^ 2 * R₀ ^ 2 / Real.log (1 / ε) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    rwa [ENNReal.toReal_pow, ENNReal.toReal_ofReal hc0] at this
  refine ⟨r, hr, fun w hw hwr => ?_⟩
  have hwim : 0 < w.im := hw
  have hθ : arg w ∈ Ioo 0 π := by
    refine ⟨lt_of_le_of_ne (arg_nonneg_iff.2 hwim.le) fun h => ?_,
      arg_lt_pi_iff.2 (Or.inr hwim.ne')⟩
    exact hwim.ne' (arg_eq_zero_iff.1 h.symm).2
  have hw_eq : (r : ℂ) * exp (arg w * I) = w := by
    rw [← hwr]; exact norm_mul_exp_arg_mul_I w
  have hi_eq : (r : ℂ) * exp (((π / 2 : ℝ) : ℂ) * I) = r * I := by
    rw [Complex.ofReal_div, Complex.ofReal_ofNat, exp_pi_div_two_mul_I]
  have hpi2 : π / 2 ∈ Ioo 0 π := ⟨by positivity, by linarith [Real.pi_pos]⟩
  have key : ENNReal.ofReal ‖fwdMapInv W s w - fwdMapInv W s (r * I)‖ ≤ L := by
    rcases le_total (arg w) (π / 2) with h | h
    · have := ofReal_norm_sub_le_semicircle hg hr0 hθ.1 h hpi2.2
      rwa [hw_eq, hi_eq, norm_sub_rev] at this
    · have := ofReal_norm_sub_le_semicircle hg hr0 hpi2.1 h hθ.2
      rwa [hw_eq, hi_eq] at this
  have hle : ‖fwdMapInv W s w - fwdMapInv W s (r * I)‖ ≤ L.toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hfin.ne).1 key
  exact (pow_le_pow_left₀ (norm_nonneg _) hle 2).trans hLsq

/-- **GEN (no path from the hull to the outside).** Rohde–Schramm Thm 4.1 (p. 19), Kemppainen
Thm 6.4 (p. 109); own adaptation via Wolff's lemma (see the module docstring). Let `W` be
continuous with `W 0 = 0` and `t ≥ 0`; assume the radial limits `f̂_s(iy) → trace W s` hold
uniformly in `s ∈ [0,t]` and `trace W` is continuous on `[0,t]`. Then no path in
`H \ trace W '' [0,t]` joins a point of `K_t` to a point of `H \ K_t`. -/
theorem gen_no_path (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    (hunif : TendstoUniformlyOn (fun (y : ℝ) (s : ℝ) => fwdMapInv W s (y * I)) (trace W)
      (𝓝[>] 0) (Icc 0 t))
    (hcont : ContinuousOn (trace W) (Icc 0 t))
    {p q : ℂ} (hp : p ∈ fwdHull W t) (hq : q ∈ H \ fwdHull W t)
    (β : Path p q) (hβ : ∀ u, β u ∈ H \ trace W '' Icc 0 t) : False := by
  set A := trace W '' Icc 0 t with hAdef
  have hAc : IsCompact A := isCompact_Icc.image_of_continuousOn hcont
  have hAne : A.Nonempty := ⟨_, 0, ⟨le_rfl, ht⟩, rfl⟩
  -- the uniform bound `R₀` of `f̂_s` on the unit half-disk
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hW.continuousOn (s := Icc 0 t))
  have hM' : ∀ x ∈ Icc (0 : ℝ) t, |W x| ≤ M := fun x hx => by
    simpa [Real.norm_eq_abs] using hM x hx
  set R₀ : ℝ := RegCont.revBound (2 * M) t 1 + 1 with hR₀
  have hR : ∀ s ∈ Icc (0 : ℝ) t, ∀ w ∈ H, ‖w‖ < 1 → ‖fwdMapInv W s w‖ < R₀ :=
    fun s hs w hw hw1 => by
      have := (RegCont.fwdMapInv_mem_H_bound hW hW0 hM' hs.1 hs.2 hw hw1.le).2
      linarith
  -- the distance `d` between the path and `A`
  obtain ⟨u₁, -, hu₁⟩ := isCompact_univ.exists_isMinOn univ_nonempty
    ((continuous_infDist_pt A).comp β.continuous).continuousOn
  set d := infDist (β u₁) A with hd
  have hdpos : 0 < d := (hAc.isClosed.notMem_iff_infDist_pos hAne).1 (hβ u₁).2
  have hdist : ∀ u, ∀ a ∈ A, d ≤ dist (β u) a := fun u a ha =>
    (hu₁ (mem_univ u)).trans (infDist_le_dist_of_mem ha)
  -- the lower bound `m` for `Im f_s q`
  obtain ⟨m, hm, hmq⟩ := CoreArc.exists_im_lower_of_isCompact hW ht isCompact_singleton
    (singleton_subset_iff.2 hq)
  -- the radial scale `y₀`
  obtain ⟨y₀, hy₀, hy₀s⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1
    ((Metric.tendstoUniformlyOn_iff.1 hunif) (d / 2) (by positivity))
  -- the choice of `ε`
  set K := 2 * π ^ 2 * R₀ ^ 2 / (d / 2) ^ 2 with hK
  set ε := min (min (1 / 2) m) (min y₀ (Real.exp (-(K + 1)))) with hεdef
  have hε0 : 0 < ε := by
    have := Real.exp_pos (-(K + 1)); have : (0 : ℝ) < y₀ := hy₀
    positivity
  have hε1 : ε < 1 := (min_le_left _ _).trans_lt ((min_le_left _ _).trans_lt (by norm_num))
  have hεm : ε ≤ m := (min_le_left _ _).trans (min_le_right _ _)
  have hεy : ε ≤ y₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hlogε : K + 1 ≤ Real.log (1 / ε) := by
    have h1 : Real.log ε ≤ -(K + 1) := by
      rw [← Real.log_exp (-(K + 1))]
      exact Real.log_le_log hε0 ((min_le_right _ _).trans (min_le_right _ _))
    rw [one_div, Real.log_inv]; linarith
  have hK0 : K * (d / 2) ^ 2 = 2 * π ^ 2 * R₀ ^ 2 := by
    rw [hK]; field_simp
  have hc : 2 * π ^ 2 * R₀ ^ 2 / Real.log (1 / ε) < (d / 2) ^ 2 := by
    have hlog : 0 < Real.log (1 / ε) := by
      have : 0 ≤ K := by rw [hK]; positivity
      linarith
    rw [div_lt_iff₀ hlog]
    have hd2 : 0 < (d / 2) ^ 2 := by positivity
    nlinarith
  -- step 1: the last point of the path in `K_t`
  set γ : ℝ → ℂ := fun x => β.extend x with hγdef
  have hγc : Continuous γ := β.continuous_extend
  have hγ : ∀ x, γ x ∈ H \ A := fun x => hβ _
  have hγu : ∀ x, ∃ u, γ x = β u := fun x => ⟨_, rfl⟩
  set S := {x ∈ Icc (0 : ℝ) 1 | γ x ∈ fwdHull W t} with hSdef
  have hSeq : S = Icc 0 1 ∩ (γ ⁻¹' (H \ fwdHull W t))ᶜ := by
    ext x
    simp only [hSdef, mem_ofPred_eq, mem_inter_iff, mem_compl_iff, mem_preimage, Set.mem_sdiff,
      not_and, not_not]
    exact and_congr_right fun _ => ⟨fun h _ => h, fun h => h (hγ x).1⟩
  have hSc : IsClosed S := by
    rw [hSeq]
    exact isClosed_Icc.inter ((FwdHolo.isOpen_compl_fwdHull hW ht).preimage hγc).isClosed_compl
  have hSbdd : BddAbove S := ⟨1, fun x hx => hx.1.2⟩
  have h0S : (0 : ℝ) ∈ S := ⟨⟨le_rfl, zero_le_one⟩, by simpa [hγdef] using hp⟩
  set u₀ := sSup S with hu₀
  have hu₀S : u₀ ∈ S := hSc.csSup_mem ⟨0, h0S⟩ hSbdd
  have hafter : ∀ x ∈ Ioc u₀ 1, γ x ∉ fwdHull W t := fun x hx hK =>
    absurd (le_csSup hSbdd ⟨⟨hu₀S.1.1.trans hx.1.le, hx.2⟩, hK⟩) (not_le.2 hx.1)
  -- step 4: the time `s`
  obtain ⟨s, hs, hp's, hsmall⟩ :=
    CoreArc.exists_small_of_mem_fwdHull hW (hγ u₀).1 ht hu₀S.2 (pow_pos hε0 2)
  have hsI : s ∈ Icc 0 t := ⟨hs.1, hs.2.le⟩
  -- step 5: the Wolff radius `r`
  obtain ⟨r, hr, hclose⟩ := exists_semicircle_close hW hW0 hs.1 (hR s hsI) hε0 hε1
  have hr0 : 0 < r := (pow_pos hε0 2).trans hr.1
  -- step 6: intermediate value theorem
  have hcomp : ∀ x ∈ Icc u₀ 1, γ x ∈ H \ fwdHull W s := by
    intro x hx
    refine ⟨(hγ x).1, ?_⟩
    rcases eq_or_lt_of_le hx.1 with h | h
    · rw [← h]; exact hp's
    · exact fun hK => hafter x ⟨h, hx.2⟩ (fwdHull_mono.1 hs.2.le hK)
  have hgc : ContinuousOn (fun x => ‖fwdMap W s (γ x)‖) (Icc u₀ 1) := fun x hx =>
    ((continuousAt_fwdMap_of_mem_complHull hW hs.1 (hcomp x hx)).comp
      hγc.continuousAt).norm.continuousWithinAt
  have hga : ‖fwdMap W s (γ u₀)‖ ≤ r := by
    have : ε ^ 2 < r := hr.1
    linarith
  have hgb : r ≤ ‖fwdMap W s (γ 1)‖ := by
    have h1 : γ 1 = q := by simp [hγdef]
    rw [h1]
    have := hmq q rfl s hsI
    have := (le_abs_self _).trans (Complex.abs_im_le_norm (fwdMap W s q))
    linarith [hr.2]
  obtain ⟨x, hx, hgx⟩ :=
    intermediate_value_Icc hu₀S.1.2 hgc ⟨hga, hgb⟩
  set z := γ x with hz
  have hzc := hcomp x hx
  set w := fwdMap W s z with hw
  have hwH : w ∈ H := FwdHolo.mapsTo_fwdMap hW hs.1 hzc
  have hzw : fwdMapInv W s w = z := fwdMapInv_fwdMap hW hW0 hs.1 hzc
  have h1 := hclose w hwH hgx
  rw [hzw] at h1
  have h1' : ‖z - fwdMapInv W s (r * I)‖ < d / 2 :=
    lt_of_pow_lt_pow_left₀ 2 (by positivity) (h1.trans_lt hc)
  have h2 : dist (trace W s) (fwdMapInv W s (r * I)) < d / 2 :=
    hy₀s ⟨hr0, hr.2.trans_le hεy⟩ s hsI
  have h3 : dist z (trace W s) < d := by
    rw [dist_comm] at h2
    calc dist z (trace W s) ≤ dist z (fwdMapInv W s (r * I)) +
          dist (fwdMapInv W s (r * I)) (trace W s) := dist_triangle _ _ _
      _ < d / 2 + d / 2 := by rw [dist_eq_norm]; exact add_lt_add h1' h2
      _ = d := by ring
  obtain ⟨u, hu⟩ := hγu x
  have := hdist u (trace W s) ⟨s, hsI, rfl⟩
  rw [← hu] at this
  linarith

end RS
end QuantumZipper
