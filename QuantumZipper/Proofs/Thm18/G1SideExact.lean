import QuantumZipper.Proofs.Thm18.G1SideWedgeFam
import QuantumZipper.Proofs.Zipper.SWCoreN2IdCc

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-SIDE (6): exactness of the pulled-back wedge field at dyadic circles, over a family

For the wedge field `w = wedgeField (lateralPart X) A Q` and a finite-parameter family of class maps
as in `G1Side.ae_wedge_transport_family`, almost surely, for all large `k`, all maps of the family
and all real centres `u ∈ [a,b]`, the dyadic average of the pulled-back field at `(u, 2^{-k})`
equals its raw value at the folded circle `fc(u, 2^{-k})` (`ae_wedge_family_exact`).

Proof: the raw value `v ↦ coordChange w (Ψ q) Q (fc(v, r))` is continuous in the centre on
`[a − r, b + r]`: it is `evalReg X (pushed circle) + ∫ profCut d(pushed circle) + Q cc`
(`G1Side.evalReg_map_fc_family_eq` for the wedge/free-field-plus-profile congruence,
`G1Side.ae_evalReg_add_fun_family`), with the three terms continuous
(`SWCore.swcN2_push_ae`, `G1Side.continuousOn_fun_push`, `SWCore.swcN2_cc_continuousOn`); the
dyadic average is the limit along the dyadic roundings of the centre. Sources: Sheffield–Wang
arXiv:1605.06171 Lemmas 3.4–3.5 (through the repository's pushed-family cores); Duplantier–Sheffield
2011 (5.1). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace G1Side

open SWCore

/-- **Congruence of the regularized values on pushed folded circles**, uniformly over the family. -/
theorem evalReg_map_fc_family_eq {ι : Type*} {Ψ : ι → ℂ → ℂ} {K : Set ι} {a b ρ M m c₀ ε₀ : ℝ}
    {y y' : FieldSample}
    (hyy : ∀ j w, w ∈ Hbar → c₀ ≤ ‖w‖ → radius j < ε₀ → avgReg y j w = avgReg y' j w)
    (hε₀ : 0 < ε₀) (hab : a ≤ b) (hcl : ∀ q ∈ K, Ψ q ∈ BdryClass a b ρ M m)
    (hsep : ∀ q ∈ K, ∀ z ∈ thickening ρ (segC a b), c₀ ≤ ‖Ψ q z‖)
    (hHb : ∀ q ∈ K, ∀ z ∈ thickening ρ (segC a b), z ∈ Hbar → Ψ q z ∈ Hbar)
    {r : ℝ} (hr : 0 < r) (hrρ : 3 * r < ρ) {q : ι} (hq : q ∈ K) {s : ℝ}
    (hs : s ∈ Icc (a - r) (b + r)) :
    evalReg y ((foldedCircle (s : ℂ) r).map (Ψ q)) =
      evalReg y' ((foldedCircle (s : ℂ) r).map (Ψ q)) := by
  have hball : closedBall (s : ℂ) r ⊆ thickening ρ (segC a b) := by
    intro z hz
    refine swcN2_ball_sub_thick (swcN2Clamp_mem hab s) (R := 2 * r) (by linarith) ?_
    have h3 : dist (s : ℂ) ((swcN2Clamp a b s : ℝ) : ℂ) = |s - swcN2Clamp a b s| := by
      rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have := swcN2Clamp_near hab hr.le hs
    rw [mem_closedBall] at hz ⊢
    linarith [dist_triangle z (s : ℂ) ((swcN2Clamp a b s : ℝ) : ℂ)]
  have hψc : ContinuousOn (Ψ q) (closedBall (s : ℂ) r) :=
    (hcl q hq).1.continuousOn.mono hball
  have hmeas : MeasurableSet {w : ℂ | w ∈ Hbar ∧ c₀ ≤ ‖w‖} :=
    (isClosed_le continuous_const Complex.continuous_im).measurableSet.inter
      (isClosed_le continuous_const continuous_norm).measurableSet
  have hae := ae_map_fc_of_forall hr.le hψc hmeas fun θ => by
    have hz := swcN2_fold_circle_mem (s := s) hr.le θ
    have hzt := hball hz
    have hzH : foldH (circleMap (s : ℂ) r θ) ∈ Hbar := by
      show 0 ≤ (foldH _).im
      unfold foldH
      split_ifs with h
      · exact h
      · simp only [Complex.conj_im]; linarith
    exact ⟨hHb q hq _ hzt hzH, hsep q hq _ hzt⟩
  unfold evalReg
  refine limUnder_congr_side ?_
  have hj : ∀ᶠ j in atTop, radius j < ε₀ :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
      (by norm_num)).eventually (gt_mem_nhds hε₀) |>.mono fun j hj => by
        simpa [radius, one_div, inv_pow] using hj
  filter_upwards [hj] with j hj
  refine integral_congr_ae ?_
  filter_upwards [hae] with w hw
  exact hyy j w hw.1 hw.2 hj

/-- The dyadic averages of the wedge field and of the free field plus the cut-off profile agree
away from `0`. -/
theorem avgReg_wedge_eq_profCut {Q₀ : ℝ} {x : FieldSample} {F : ℂ × ℝ → ℝ}
    (hG : WedgeTK.GoodRad x F)
    (hraw : ∀ (n : ℕ) (z : ℂ), z ∈ Hbar → ∀ k : ℕ,
      x (foldedCircle (dyadicRoundC n z) (radius k)) = F (dyadicRoundC n z, radius k))
    {A : ℝ → ℝ} (hA : Continuous A) {c₀ : ℝ} (hc₀ : 0 < c₀) :
    ∀ j w, w ∈ Hbar → c₀ ≤ ‖w‖ → radius j < c₀ / 4 →
      avgReg (wedgeField (lateralPart x) A Q₀) j w =
        avgReg (x + ofFun (profCut x A Q₀ (c₀ / 2))) j w := by
  intro j w hw hwc hj
  have hne : ‖w‖ ≠ radius j := by
    intro h; rw [h] at hwc; linarith
  rw [WedgeCan.avgReg_wedgeField_eq hG hraw hA Q₀ hw hne]
  exact avgReg_add_ofFun_congr hc₀ (fun z hz => (profCut_eq hz).symm) hwc hj

/-- A dyadic average at a real centre equals the raw value when the raw value is continuous in
the (real) centre. -/
theorem avgReg_eq_of_continuousOn {Z : FieldSample} {a b : ℝ} {k : ℕ}
    (hcont : ContinuousOn (fun v : ℝ => Z (foldedCircle (v : ℂ) (radius k)))
      (Icc (a - radius k) (b + radius k))) {u : ℝ} (hu : u ∈ Icc a b) :
    avgReg Z k (u : ℂ) = Z (foldedCircle (u : ℂ) (radius k)) := by
  have hr : 0 < radius k := radius_pos k
  have huI : u ∈ Icc (a - radius k) (b + radius k) :=
    ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hround : Tendsto (fun n : ℕ => dyadicRound n u) atTop
      (𝓝[Icc (a - radius k) (b + radius k)] u) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _)
        (fun n => (CircleCont.abs_dyadicRound_sub_le n u)) ?_)
      simp_rw [one_div, ← inv_pow]
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    · have hn : ∀ᶠ n : ℕ in atTop, (1 : ℝ) / 2 ^ n ≤ radius k := by
        filter_upwards [eventually_ge_atTop k] with n hn
        unfold radius
        rw [one_div, ← inv_pow]
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
      filter_upwards [hn] with n hn
      have h1 := CircleCont.abs_dyadicRound_sub_le n u
      rw [abs_le] at h1
      exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hT := ((hcont u huI).tendsto).comp hround
  unfold avgReg
  have e : (fun n => Z (foldedCircle (dyadicRoundC n (u : ℂ)) (radius k))) =
      (fun v : ℝ => Z (foldedCircle (v : ℂ) (radius k))) ∘ (fun n : ℕ => dyadicRound n u) := by
    funext n
    simp only [comp_apply, CoordChange.dyadicRoundC_ofReal]
  rw [e]
  exact hT.limUnder_eq

set_option maxHeartbeats 800000 in
/-- **Exactness of the pulled-back wedge field at dyadic circles, uniformly over a family, a.s.** -/
theorem ae_wedge_family_exact {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Qc γ)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ} (hX : IsFreeGFFModConstH X P')
    (hA : IsWedgeProcess α (Qc γ) A P')
    {n : ℕ} {Ψ : (Fin n → ℝ) → ℂ → ℂ} {K : Set (Fin n → ℝ)} {a b ρ M m L : ℝ}
    {Kπ : ℝ≥0} {π : (Fin n → ℝ) → Fin n → ℝ} (hab : a < b) (hρ : 0 < ρ)
    (hm : 0 < m) (hL : 0 ≤ L)
    (hcl : ∀ q ∈ K, Ψ q ∈ BdryClass a b ρ M m)
    (hlip : ∀ q ∈ K, ∀ q' ∈ K, ∀ z ∈ thickening ρ (segC a b),
      ‖Ψ q z - Ψ q' z‖ ≤ L * ‖q - q'‖)
    (hπ : LipschitzWith Kπ π) (hπK : ∀ q, π q ∈ K) (hπid : ∀ q ∈ K, π q = q)
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hsep : ∀ q ∈ K, ∀ z ∈ thickening ρ (segC a b), c₀ ≤ ‖Ψ q z‖)
    (hHb : ∀ q ∈ K, ∀ z ∈ thickening ρ (segC a b), z ∈ Hbar → Ψ q z ∈ Hbar) :
    ∀ᵐ ω ∂P', ∀ᶠ k in atTop, ∀ q ∈ K, (∀ u ∈ Icc a b,
      avgReg (coordChange (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ)) (Ψ q)
          (Qc γ)) k (u : ℂ) =
        coordChange (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ)) (Ψ q) (Qc γ)
          (foldedCircle (u : ℂ) (radius k))) ∧
      ContinuousOn (fun u : ℝ => avgReg (coordChange (wedgeField (lateralPart (X ω))
        (fun t => A t ω) (Qc γ)) (Ψ q) (Qc γ)) k (u : ℂ)) (Icc a b) := by
  obtain ⟨r₂, hr₂, hadd⟩ := ae_evalReg_add_fun_family hab hρ hm hcl hL hlip hπ hπK hπid hX
  obtain ⟨r₃, hr₃, hpush⟩ := swcN2_push_ae hab hρ hm hcl hL hlip hπ hπK hπid hX
  obtain ⟨G, hG⟩ := WedgeTK.exists_isRegVersion hX
  have hsmall : ∀ᶠ k in atTop, radius k < min r₂ r₃ ∧ 3 * radius k < ρ ∧
      2 * radius k ≤ ρ / 8 ∧ 32 * (|M| + 1) / ρ ^ 2 * (2 * radius k) ≤ m / 2 := by
    have ht : Tendsto radius atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have h1 := ht.eventually (gt_mem_nhds (lt_min hr₂ hr₃))
    have h2 := (ht.const_mul 3).eventually
      (gt_mem_nhds (show (3 : ℝ) * 0 < ρ by rw [mul_zero]; exact hρ))
    have h3 := (ht.const_mul 2).eventually
      (ge_mem_nhds (show (2 : ℝ) * 0 < ρ / 8 by rw [mul_zero]; positivity))
    have h4 := ((ht.const_mul 2).const_mul (32 * (|M| + 1) / ρ ^ 2)).eventually
      (ge_mem_nhds (show 32 * (|M| + 1) / ρ ^ 2 * ((2 : ℝ) * 0) < m / 2 by
        rw [mul_zero, mul_zero]; positivity))
    filter_upwards [h1, h2, h3, h4] with k k1 k2 k3 k4 using ⟨k1, k2, k3, k4⟩
  have hk_ae : ∀ᵐ ω ∂P', ∀ k : ℕ, radius k < min r₂ r₃ →
      (∀ g : ℂ → ℝ, Continuous g → ∀ q ∈ K, ∀ t ∈ Icc (a - radius k) (b + radius k),
        evalReg (X ω + ofFun g) ((foldedCircle (t : ℂ) (radius k)).map (Ψ q)) =
          evalReg (X ω) ((foldedCircle (t : ℂ) (radius k)).map (Ψ q)) +
            ∫ w, g w ∂((foldedCircle (t : ℂ) (radius k)).map (Ψ q))) ∧
      ContinuousOn (fun x : (Fin n → ℝ) × ℝ =>
          evalReg (X ω) ((foldedCircle (x.2 : ℂ) (radius k)).map (Ψ x.1)))
        (K ×ˢ Icc (a - radius k) (b + radius k)) := by
    refine ae_all_iff.2 fun k => ?_
    by_cases hk : radius k < min r₂ r₃
    · have hk2 : radius k ∈ Ioo 0 r₂ := ⟨radius_pos k, lt_of_lt_of_le hk (min_le_left _ _)⟩
      have hk3 : radius k ∈ Ioo 0 r₃ := ⟨radius_pos k, lt_of_lt_of_le hk (min_le_right _ _)⟩
      filter_upwards [hadd _ hk2, (hpush _ hk3).1] with ω h1 h2 _ using ⟨h1, h2⟩
    · exact ae_of_all _ fun ω h => absurd h hk
  filter_upwards [hk_ae, hG.ae_good, WedgeCan.ae_raw_dyadic hG,
    WedgeCan4.ae_continuous_wedgeProcess hA] with ω hω hgood hraw hAc
  filter_upwards [hsmall] with k ⟨hk1, hk3, hk8, hkm⟩ q hq
  set r := radius k with hrdef
  have hr : 0 < r := radius_pos k
  obtain ⟨hAdd, hCont⟩ := hω k hk1
  set g := profCut (X ω) (fun t => A t ω) (Qc γ) (c₀ / 2) with hgdef
  have hgc : Continuous g := continuous_profCut hgood hAc (Qc γ) (by positivity)
  set w := wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ) with hw
  -- the raw value as a continuous function of the centre
  have hval : ∀ v ∈ Icc (a - r) (b + r), coordChange w (Ψ q) (Qc γ) (foldedCircle (v : ℂ) r) =
      evalReg (X ω) ((foldedCircle (v : ℂ) r).map (Ψ q)) +
        ∫ z, g z ∂((foldedCircle (v : ℂ) r).map (Ψ q)) + Qc γ * CoordChange.cc (Ψ q) v r := by
    intro v hv
    rw [CoordChange.coordChange_fc, ← hAdd g hgc q hq v hv]
    congr 1
    exact evalReg_map_fc_family_eq (avgReg_wedge_eq_profCut hgood hraw hAc hc₀)
      (by positivity) hab.le hcl hsep hHb hr hk3 hq hv
  have hc1 : ContinuousOn (fun v : ℝ => evalReg (X ω) ((foldedCircle (v : ℂ) r).map (Ψ q)))
      (Icc (a - r) (b + r)) :=
    hCont.comp (continuousOn_const.prodMk continuousOn_id) fun v hv => ⟨hq, hv⟩
  have hc2 := continuousOn_fun_push hgc (hcl q hq) hab.le hr hk3
  have hc3 := swcN2_cc_continuousOn (hcl q hq) hab.le hρ hm hr hk8 hkm
  have hcont : ContinuousOn (fun v : ℝ => coordChange w (Ψ q) (Qc γ) (foldedCircle (v : ℂ) r))
      (Icc (a - r) (b + r)) :=
    ((hc1.add hc2).add (continuousOn_const.mul hc3)).congr fun v hv => hval v hv
  have hex : ∀ u ∈ Icc a b, avgReg (coordChange w (Ψ q) (Qc γ)) k (u : ℂ) =
      coordChange w (Ψ q) (Qc γ) (foldedCircle (u : ℂ) (radius k)) := by
    intro u hu
    exact avgReg_eq_of_continuousOn hcont hu
  refine ⟨hex, (hcont.mono fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩).congr
    fun u hu => hex u hu⟩
end G1Side
end QuantumZipper
