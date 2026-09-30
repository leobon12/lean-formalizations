import QuantumZipper.Proofs.RS.OnePointFinalKoebe

/-!
# THM11 AD-2, deterministic part: a point with conformal radius bounded below is not on the trace

Let `W` be a continuous driver with `W 0 = 0` whose trace `η = trace W` is continuous, is the
radial limit `η(s) = lim_{y↓0} f̂_s(iy)` at every time, and generates the hulls
(`H \ K_t` is the component of `H \ η[0,t]` containing `M i` for `M` large; this is
`Blueprint.RohdeSchrammTraceGen` on its good event). If the log conformal radius of `a` stays
`≥ log Im a − M` at all alive times `t ≤ T`, then `a ∉ η[0,T]`
(`notMem_trace_image_of_logCR_bound`).

Proof. By Koebe's one-quarter theorem (`RS.koebe_logCR_le_dist`, EXT-CA K5a; Garnett–Marshall,
*Harmonic Measure*, Cor. I.4.4, p. 19; Pommerenke, *Boundary Behaviour of Conformal Maps*,
Cor 1.4, p. 9) the trace stays at distance `≥ ρ > 0` from `a` at alive times. If `a` is alive
at time `s`, `η(s) ≠ a` directly. Otherwise let `τ ≤ s` be the swallowing time of `a`; by
continuity `η[0,τ]` misses the ball `B(a,ρ)`, so `B(a,ρ)` lies in one component of
`H \ η[0,τ]`, which is not the unbounded one because `a ∈ K_τ` (generation). So
`B(a,ρ) ∩ (H \ K_τ) = ∅`, and `η(s)`, a limit of points `f̂_s(iy) ∈ H \ K_s ⊆ H \ K_τ`, is not in
`B(a,ρ)`. This is the deterministic half of "points are swallowed, not hit" (Rohde–Schramm,
*Basic properties of SLE*, Ann. Math. 161 (2005), Thm 6.4, pp. 29–31; Kemppainen,
*Schramm–Loewner Evolution*, Prop 5.6, p. 85); the arrangement with the conformal radius is our
own elementary argument.
-/

noncomputable section

open Set Filter Topology Metric
open scoped ENNReal

namespace QuantumZipper
namespace Thm11Area

open RS FwdClock

theorem notMem_trace_image_of_logCR_bound {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    (hcont : ContinuousOn (trace W) (Ici 0))
    (hlim : ∀ s, 0 ≤ s →
      Tendsto (fun y : ℝ => fwdMapInv W s (y * Complex.I)) (𝓝[>] 0) (𝓝 (trace W s)))
    (hgen : ∀ t, 0 ≤ t → ∀ M : ℝ, (∀ s ∈ Icc 0 t, ‖trace W s‖ < M) →
      H \ fwdHull W t = connectedComponentIn (H \ trace W '' Icc 0 t) (M * Complex.I))
    {a : ℂ} (ha : a ∈ H) {T M : ℝ}
    (hM : ∀ t, 0 ≤ t → t ≤ T → a ∉ fwdHull W t → Real.log a.im - M ≤ fwdLogCR W t a) :
    a ∉ trace W '' Icc 0 T := by
  have ha0 : 0 < a.im := ha
  set r := CA.Koebe.koebeCovConst * Real.exp (Real.log a.im - M) with hrdef
  have hr : 0 < r := mul_pos CA.Koebe.koebeCovConst_pos (Real.exp_pos _)
  have hK : ∀ t, 0 ≤ t → t ≤ T → a ∉ fwdHull W t → r ≤ dist a (trace W t) :=
    fun t ht0 htT hat =>
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (hM t ht0 htT hat))
        CA.Koebe.koebeCovConst_pos.le).trans
      (koebe_logCR_le_dist hW hW0 ht0 (hlim t ht0) ⟨ha, hat⟩)
  rintro ⟨s, ⟨hs0, hsT⟩, hsa⟩
  by_cases has : a ∈ fwdHull W s
  swap
  · have := hK s hs0 hsT has
    rw [hsa, dist_self] at this
    linarith
  have hτfin : swallowTime W a ≤ ENNReal.ofReal s := has.2
  set τ := (swallowTime W a).toReal with hτdef
  have hτeq : swallowTime W a = ENNReal.ofReal τ :=
    (ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hτfin)).symm
  have hτs : τ ≤ s := by
    rw [hτeq] at hτfin; exact (ENNReal.ofReal_le_ofReal_iff hs0).1 hτfin
  have hτpos : 0 < τ := by
    have := swallowTime_pos hW ha0
    rw [hτeq] at this
    exact ENNReal.ofReal_pos.1 this
  have halive : ∀ t, 0 ≤ t → t < τ → a ∉ fwdHull W t := fun t ht0 htτ hat => by
    have := hat.2
    rw [hτeq] at this
    exact absurd ((ENNReal.ofReal_le_ofReal_iff ht0).1 this) (not_le.2 htτ)
  set ρ := min r a.im with hρdef
  have hρ : 0 < ρ := lt_min hr ha0
  have hlt : ∀ t ∈ Ico 0 τ, ρ ≤ dist a (trace W t) := fun t ht =>
    (min_le_left _ _).trans (hK t ht.1 (ht.2.le.trans (hτs.trans hsT)) (halive t ht.1 ht.2))
  have hfar : ∀ t ∈ Icc 0 τ, ρ ≤ dist a (trace W t) := by
    intro t ht
    rcases eq_or_lt_of_le ht.2 with h | h
    · rw [h]
      have hca : ContinuousAt (trace W) τ := hcont.continuousAt (Ici_mem_nhds hτpos)
      have htd : Tendsto (fun t => dist a (trace W t)) (𝓝[<] τ) (𝓝 (dist a (trace W τ))) :=
        (tendsto_const_nhds.dist hca).mono_left nhdsWithin_le_nhds
      refine ge_of_tendsto htd ?_
      filter_upwards [Ioo_mem_nhdsLT hτpos] with t ht'
      exact hlt t ⟨ht'.1.le, ht'.2⟩
    · exact hlt t ⟨ht.1, h⟩
  set S := H \ trace W '' Icc 0 τ with hSdef
  have hball : ball a ρ ⊆ S := by
    intro b hb
    refine ⟨?_, ?_⟩
    · have h1 : |b.im - a.im| ≤ dist b a := by
        rw [Complex.dist_eq]; exact (Complex.abs_im_le_norm (b - a)).trans_eq' (by simp)
      have h2 : dist b a < ρ := hb
      have h3 : ρ ≤ a.im := min_le_right _ _
      show 0 < b.im
      have := (abs_lt.1 (h1.trans_lt (h2.trans_le h3))).1
      linarith
    · rintro ⟨t, ht, hbt⟩
      have := hfar t ht
      rw [hbt, dist_comm] at this
      exact absurd hb (not_lt.2 this)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := τ)).exists_bound_of_continuousOn
    (hcont.mono Icc_subset_Ici_self)
  have hgτ := hgen τ hτpos.le (C + 1) fun t ht => (hC t ht).trans_lt (lt_add_one C)
  have haK : a ∈ fwdHull W τ := ⟨ha, hτeq.le⟩
  have hdisj : ∀ b ∈ ball a ρ, b ∉ H \ fwdHull W τ := by
    intro b hb hbD
    rw [hgτ] at hbD
    have e := connectedComponentIn_eq hbD
    have hsub : ball a ρ ⊆ connectedComponentIn S b :=
      (convex_ball a ρ).isPreconnected.subset_connectedComponentIn hb hball
    have haD : a ∈ H \ fwdHull W τ := by
      rw [hgτ, e]; exact hsub (mem_ball_self hρ)
    exact haD.2 haK
  -- `η(s)` is a limit of points of `H \ K_s ⊆ H \ K_τ`
  have hev1 : ∀ᶠ y : ℝ in 𝓝[>] (0 : ℝ), fwdMapInv W s ((y : ℂ) * Complex.I) ∈ ball a ρ := by
    have := hlim s hs0
    rw [hsa] at this
    exact this (ball_mem_nhds a hρ)
  have hev2 : ∀ᶠ y : ℝ in 𝓝[>] (0 : ℝ), fwdMapInv W s ((y : ℂ) * Complex.I) ∈ H \ fwdHull W τ := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hyH : (y : ℂ) * Complex.I ∈ H := by
      show 0 < ((y : ℂ) * Complex.I).im
      simpa using hy
    have hm := fwdMapInv_mem_compl_fwdHull hW hW0 hs0 hyH
    refine ⟨hm.1, fun hK' => hm.2 ⟨hK'.1, hK'.2.trans (ENNReal.ofReal_le_ofReal hτs)⟩⟩
  obtain ⟨y, hy1, hy2⟩ := (hev1.and hev2).exists
  exact hdisj _ hy1 hy2

end Thm11Area
end QuantumZipper
