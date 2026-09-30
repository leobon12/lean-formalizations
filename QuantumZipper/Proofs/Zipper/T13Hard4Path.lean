import QuantumZipper.Proofs.Zipper.T13Hard4PathCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# T13-HARD4: `HitPathIndStmt` from the uniform translation smoothness of first passage laws

`D3Plus.hitPathInd_of_transUnif : HitTransUnifStmt → HitPathIndStmt`. The re-centred path at the
first passage time of `Xc_L = L + √2 b + (α − Q)·` below `0` is asymptotically independent of that
time: strong Markov at the first visit of the intermediate level `M` (`T13Path.tv_perL`,
Duplantier–Miller–Sheffield arXiv:1409.7055, proof of Prop. 4.7, p. 78; Le Gall GTM 274,
Thm 2.20), with the choices `M` (the path does not fall by `M` within time `S`), `N` (the restarted
path passes below `0` by time `N`), then `L` large (translation defect of the law of `T_{L−M}` on
`[0, N]` small) and `n` large (the level `M − L` is reached before `n`); all Gaussian tails by the
Doob bound `BMOsc.bmOsc_tail`.

The remaining input is the one-dimensional statement `HitTransUnifStmt`: the law of the first
passage time `T_L` is asymptotically invariant, in total variation, under translations by
`x ∈ [0, N]`, uniformly (the inverse Gaussian law `IG(L/ν, L²/2)` has spread `≍ √L`;
Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, §3.5.C, (5.12)). Own assembly.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-- **Uniform translation smoothness of the first passage law** (one-dimensional). For a Brownian
motion and `α < Q`, the law of `Tc α Q L b` is asymptotically invariant in total variation under
translations by `x ∈ [0, N]`, uniformly in `x`, as `L → ∞`. -/
def HitTransUnifStmt : Prop :=
  ∀ (α Q : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (b : ℝ≥0 → Ω → ℝ), IsBrownianReal b P → α < Q → ∀ N : ℝ,
    Tendsto (fun L => ⨆ x ∈ Icc (0 : ℝ) N, TV.tvDist (P.map fun ω => ZoomRadial.Tc α Q L b ω)
      ((P.map fun ω => ZoomRadial.Tc α Q L b ω).map fun t => t + x)) atTop (𝓝 0)

/-- A Gaussian tail `2 e^{−x²/(2s)}` is `≤ δ` once `x² ≥ (2/δ)(2s)`. -/
theorem tail_small_path {δ x s : ℝ} (hδ : 0 < δ) (hs : 0 < s) (h : 2 / δ * (2 * s) ≤ x ^ 2) :
    ENNReal.ofReal (2 * Real.exp (-(x ^ 2) / (2 * s))) ≤ ENNReal.ofReal δ := by
  refine ENNReal.ofReal_le_ofReal ?_
  set y := x ^ 2 / (2 * s) with hy
  have hy2 : 2 / δ ≤ y := by rw [hy, le_div_iff₀ (by positivity)]; exact h
  have hexp : y + 1 ≤ Real.exp y := Real.add_one_le_exp y
  have hneg : -(x ^ 2) / (2 * s) = -y := by rw [hy, neg_div]
  rw [hneg, Real.exp_neg]
  have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy2
  have hpos : 0 < Real.exp y := Real.exp_pos y
  rw [← div_eq_mul_inv, div_le_iff₀ hpos]
  have : 2 ≤ δ * (y + 1) := by
    have h1 : 2 / δ * δ = 2 := div_mul_cancel₀ 2 hδ.ne'
    nlinarith
  nlinarith

/-- The algebra of the choice of a large horizon `m`. -/
theorem horizon_ok {ν δ c m : ℝ} (hν : 0 < ν) (hδ : 0 < δ) (hc : 0 ≤ c)
    (hm : 2 * c / ν + 64 / (ν ^ 2 * δ) ≤ m) :
    c < ν * m ∧ 2 / δ * (2 * m) ≤ ((ν * m - c) / 2) ^ 2 := by
  have hA : 0 < 64 / (ν ^ 2 * δ) := by positivity
  have hB : 0 ≤ 2 * c / ν := by positivity
  have hm0 : 0 < m := by linarith
  have h1 : 2 * c ≤ ν * m - ν * (64 / (ν ^ 2 * δ)) := by
    have : 2 * c / ν ≤ m - 64 / (ν ^ 2 * δ) := by linarith
    rw [div_le_iff₀ hν] at this; nlinarith
  have hνA : ν * (64 / (ν ^ 2 * δ)) = 64 / (ν * δ) := by field_simp
  have hpos64 : 0 < 64 / (ν * δ) := by positivity
  refine ⟨by nlinarith, ?_⟩
  have hu : ν * m / 4 ≤ (ν * m - c) / 2 := by nlinarith
  have hu0 : 0 ≤ ν * m / 4 := by positivity
  have hsq : (ν * m / 4) ^ 2 ≤ ((ν * m - c) / 2) ^ 2 := pow_le_pow_left₀ hu0 hu 2
  have hmA : 64 / (ν ^ 2 * δ) ≤ m := by linarith
  have key : 2 / δ * (2 * m) ≤ (ν * m / 4) ^ 2 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < ν ^ 2 * δ)] at hmA
    have e : 2 / δ * (2 * m) = 4 * m / δ := by ring
    rw [e, div_le_iff₀ hδ]
    nlinarith
  exact key.trans hsq

/-- **`HitPathIndStmt` from the uniform translation smoothness.** -/
theorem hitPathInd_of_transUnif (h : HitTransUnifStmt) : HitPathIndStmt := by
  intro α Q Ω _ P _ b hb hQ S hS
  obtain ⟨W, hWm, hWc, hW0, hW, hWb⟩ := RS.exists_good_version0 hb
  have hgood : Williams.GoodBM W P := ⟨hW.toIsPreBrownianReal, hWm, hWc, hW0⟩
  -- replace `b` by its good version
  have hcongr : ∀ L, ∀ᵐ ω ∂P, (ZoomRadial.trunc S (ZoomRadial.zoomRadial α Q b L ω),
      ZoomRadial.Tc α Q L b ω) = (ZoomRadial.trunc S (ZoomRadial.zoomRadial α Q W L ω),
      ZoomRadial.Tc α Q L W ω) := by
    intro L
    filter_upwards [hWb] with ω hω
    have hX : ∀ c t, ZoomRadial.Xc α Q c b ω t = ZoomRadial.Xc α Q c W ω t := by
      intro c t; simp only [ZoomRadial.Xc, hω]
    have hT : ZoomRadial.Tc α Q L b ω = ZoomRadial.Tc α Q L W ω := by
      simp only [ZoomRadial.Tc, hX]
    refine Prod.ext ?_ hT
    funext s
    simp only [ZoomRadial.trunc, ZoomRadial.zoomRadial, hT, hX]
  have hmapJ : ∀ L, (P.map fun ω => (ZoomRadial.trunc S (ZoomRadial.zoomRadial α Q b L ω),
      ZoomRadial.Tc α Q L b ω)) = P.map fun ω =>
        (ZoomRadial.trunc S (ZoomRadial.zoomRadial α Q W L ω), ZoomRadial.Tc α Q L W ω) :=
    fun L => Measure.map_congr (hcongr L)
  have hmap1 : ∀ L, (P.map fun ω => ZoomRadial.trunc S (ZoomRadial.zoomRadial α Q b L ω)) =
      P.map fun ω => ZoomRadial.trunc S (ZoomRadial.zoomRadial α Q W L ω) :=
    fun L => Measure.map_congr ((hcongr L).mono fun ω h => congrArg Prod.fst h)
  have hmap2 : ∀ L, (P.map fun ω => ZoomRadial.Tc α Q L b ω) =
      P.map fun ω => ZoomRadial.Tc α Q L W ω :=
    fun L => Measure.map_congr ((hcongr L).mono fun ω h => congrArg Prod.snd h)
  simp only [hmapJ, hmap1, hmap2]
  -- the ε-argument
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  set ν := Q - α with hνdef
  have hν : 0 < ν := by rw [hνdef]; linarith
  obtain ⟨δ, hδ, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ 15 * ENNReal.ofReal δ ≤ ε := by
    by_cases htop : ε = ⊤
    · exact ⟨1, one_pos, by rw [htop]; exact le_top⟩
    · have hε0 : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
      refine ⟨ε.toReal / 15, by positivity, le_of_eq ?_⟩
      rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_toReal htop]
      rw [show ENNReal.ofReal 15 = (15 : ℝ≥0∞) by norm_num]
      exact ENNReal.mul_div_cancel (by norm_num) (by norm_num)
  -- the level `M`
  set S1 : ℝ≥0 := ⟨S + 1, by linarith⟩ with hS1def
  have hS1v : (S1 : ℝ) = S + 1 := rfl
  have hS1 : S ≤ (S1 : ℝ) := by rw [hS1v]; linarith
  have hS1p : 0 < S1 := by
    rw [← NNReal.coe_pos, hS1v]; linarith
  set K : ℝ := 1 + 4 * (S1 : ℝ) / δ with hK
  have hK1 : 1 ≤ K := by have : 0 ≤ 4 * (S1 : ℝ) / δ := by positivity
                         linarith
  set M : ℝ := ν * S + 2 * K with hMdef
  have hMS : ν * S < M := by linarith
  have hM0 : 0 < M := by have : 0 ≤ ν * S := by positivity
                         linarith
  have htS : ENNReal.ofReal (2 * Real.exp (-((M - ν * S) / 2) ^ 2 / (2 * (S1 : ℝ)))) ≤
      ENNReal.ofReal δ := by
    refine tail_small_path hδ (by exact_mod_cast hS1p) ?_
    have hx : (M - ν * S) / 2 = K := by rw [hMdef]; ring
    rw [hx]
    have : 4 * (S1 : ℝ) / δ ≤ K := by linarith
    have e : 2 / δ * (2 * (S1 : ℝ)) = 4 * (S1 : ℝ) / δ := by ring
    rw [e]; nlinarith
  -- the horizon `N`
  set N0 : ℝ := 2 * M / ν + 64 / (ν ^ 2 * δ) with hN0
  set N : ℝ≥0 := ⟨N0, by positivity⟩ with hNdef
  have hNval : (N : ℝ) = N0 := rfl
  obtain ⟨hNM, hNx⟩ := horizon_ok (c := M) (m := N) hν hδ hM0.le (by rw [hNval])
  have hNpos : (0 : ℝ) < N := by rw [hNval]; positivity
  have htN : ENNReal.ofReal (2 * Real.exp (-((ν * N - M) / 2) ^ 2 / (2 * (N : ℝ)))) ≤
      ENNReal.ofReal δ := tail_small_path hδ hNpos hNx
  -- the level `L`
  have hSup := (h α Q P W hW hQ N).comp (tendsto_atTop_add_const_right atTop (-M) tendsto_id)
  have hev := (ENNReal.tendsto_nhds_zero.1 hSup _ (ENNReal.ofReal_pos.2 hδ)).and
    (eventually_gt_atTop (M + 1))
  filter_upwards [hev] with L ⟨hLsup, hLM⟩
  simp only [Function.comp_apply, ← sub_eq_add_neg] at hLsup
  -- the cap `n`
  set n : ℕ := ⌈2 * (L - M) / ν + 64 / (ν ^ 2 * δ)⌉₊ with hndef
  have hn : 2 * (L - M) / ν + 64 / (ν ^ 2 * δ) ≤ (n : ℝ) := Nat.le_ceil _
  obtain ⟨hnL, hnx⟩ := horizon_ok (c := L - M) (m := n) hν hδ (by linarith) hn
  have hnpos : (0 : ℝ) < n := by
    have : 0 < 64 / (ν ^ 2 * δ) := by positivity
    have : 0 ≤ 2 * (L - M) / ν := by
      have : 0 ≤ L - M := by linarith
      positivity
    linarith
  have htn : ENNReal.ofReal (2 * Real.exp (-((ν * n - (L - M)) / 2) ^ 2 /
      (2 * ((n : ℝ≥0) : ℝ)))) ≤ ENNReal.ofReal δ := by
    have e : ((n : ℝ≥0) : ℝ) = (n : ℝ) := by simp
    rw [e]; exact tail_small_path hδ hnpos hnx
  have hmain := T13Path.tv_perL hgood hQ n hS1 hS1p hMS hM0 hNM (by linarith) hnL
  refine hmain.trans ((add_le_add (add_le_add (add_le_add
    (mul_le_mul_right htn 5) (mul_le_mul_right htS 3)) (mul_le_mul_right htN 5))
    (mul_le_mul_right hLsup 2)).trans ?_)
  calc 5 * ENNReal.ofReal δ + 3 * ENNReal.ofReal δ + 5 * ENNReal.ofReal δ +
        2 * ENNReal.ofReal δ = 15 * ENNReal.ofReal δ := by ring
    _ ≤ ε := hδε

end D3Plus
end QuantumZipper
