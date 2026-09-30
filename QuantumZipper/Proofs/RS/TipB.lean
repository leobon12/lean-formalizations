import QuantumZipper.Proofs.RS.Simple
import QuantumZipper.Proofs.Complex.CaraExt
import QuantumZipper.Proofs.Complex.TopoSep
import QuantumZipper.Proofs.Complex.BasicsCayley

/-!
# EXT-RS node TIP-b: the tip never returns to `0` (all κ ≤ 4), and SIM, HULL for κ ≤ 4

Blueprint `blueprint/EXT_RS_BLUEPRINT.md` §4, node **TIP-b** (task RS-TIP-SIM).

Deterministic half of RS Thm 4.1 / Kemppainen Thm 6.4 at a fixed time `u > 0`, for a driver
with the TR4 conclusion (`RadialGood`): with `A = η [0,u]`,
`D = cayley '' (ℍ \ K_u)` and `E = sphere 0 1 ∪ cayley '' A`,

* `carHyp_tip`: `ψ = cayley ∘ f̂_u` satisfies the hypotheses `(Hψ)` of EXT-CA C3; the key
  inclusion `frontier D ⊆ E` is GEN-b (`frontier_compl_fwdHull_inter_H_subset`), and
  `E ∩ D = ∅` is TR5 (`η s ∈ K_s ∪ ℝ`);
* `ulc_tipE`: `E` is ULC (circle plus the continuous image of `[0,1]`, EXT-CA T7);
* `tendsto_fwdMapInv_nhdsWithin_H_zero`: C3 (`CA.Car.continuousOn_extension`) gives the
  continuous extension, hence `f̂_u(w) → η u` as `w → 0` in `ℍ`.

Then **TIP** `ae_sleTrace_ne_zero` for all `0 < κ ≤ 4`, and **SIM** / **HULL** for `κ ≤ 4`
without hypotheses (`ae_sleTrace_simple_of_le_four`, `ae_fwdHull_eq_sleTrace_image_of_le_four`).

Sources: Rohde–Schramm, *Basic properties of SLE*, Ann. Math. 161 (2005), Thm 6.1 and its
proof (p. 23), Thm 4.1 (p. 19: "`g_t⁻¹` extends continuously to `ℍ̄`"); Kemppainen (2017),
Thm 6.4 (p. 109), p. 80 (5.5); Pommerenke, *Boundary Behaviour of Conformal Maps*, Thm 2.1
(Carathéodory's continuity theorem, via EXT-CA C3). The Cayley set-up follows EXT-CA
`CaraR3Hyp.lean` (own elementary plane topology).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Complex Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace RS

open CA CA.Topo CA.Car

variable {W : ℝ → ℝ} {u : ℝ}

theorem trace_mem_Hbar (hW : RadialGood W) {s : ℝ} (hs : 0 ≤ s) : trace W s ∈ Hbar := by
  rcases trace_mem_fwdHull_or_real hW.1 hW.2.1 hs (hW.tendsto hs) with h | h
  · exact H_subset_Hbar ((fwdHull_mono.2 s) h)
  · show (0 : ℝ) ≤ (trace W s).im
    rw [h]

theorem trace_mem_fwdHull_of_mem_H (hW : RadialGood W) {s : ℝ} (hs : 0 ≤ s) (hsu : s ≤ u)
    (hH : trace W s ∈ H) : trace W s ∈ fwdHull W u := by
  rcases trace_mem_fwdHull_or_real hW.1 hW.2.1 hs (hW.tendsto hs) with h | h
  · exact fwdHull_mono.1 hsu h
  · exact absurd h (ne_of_gt hH)

/-- The bounded domain `cayley '' (ℍ \ K_u)`. -/
def tipD (W : ℝ → ℝ) (u : ℝ) : Set ℂ := cayley '' (H \ fwdHull W u)

/-- The circle plus the Cayley image of the trace on `[0,u]`. -/
def tipE (W : ℝ → ℝ) (u : ℝ) : Set ℂ := sphere 0 1 ∪ cayley '' (trace W '' Icc 0 u)

theorem tipD_eq : tipD W u = ball 0 1 ∩ cayleyInv ⁻¹' (H \ fwdHull W u) := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hzI := add_I_ne_zero_of_im_nonneg (le_of_lt (show (0 : ℝ) < z.im from hz.1))
    refine ⟨cayley_mem_ball hz.1, ?_⟩
    show cayleyInv (cayley z) ∈ H \ fwdHull W u
    rwa [cayleyInv_cayley hzI]
  · rintro ⟨hw, hz⟩
    have hw1 : w ≠ 1 := by rintro rfl; simp at hw
    exact ⟨cayleyInv w, hz, cayley_cayleyInv hw1⟩

theorem ne_one_of_mem_ball {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : w ≠ 1 := by
  rintro rfl; simp at hw

theorem isOpen_tipD (hW : RadialGood W) (hu : 0 < u) : IsOpen (tipD W u) := by
  rw [tipD_eq]
  exact (continuousOn_cayleyInv.mono fun w hw => ne_one_of_mem_ball hw).isOpen_inter_preimage
    isOpen_ball (FwdHolo.isOpen_compl_fwdHull hW.1 hu.le)

theorem tipD_subset_ball : tipD W u ⊆ ball 0 1 := by
  rintro _ ⟨z, hz, rfl⟩
  exact cayley_mem_ball hz.1

theorem trace_image_eq_Icc01 (hu : 0 < u) :
    trace W '' Icc 0 u = (fun r => trace W (u * r)) '' Icc 0 1 := by
  rw [show (fun r => trace W (u * r)) = trace W ∘ (u * ·) from rfl, image_comp,
    image_mul_left_Icc hu.le zero_le_one]
  simp

theorem continuousOn_cayley_trace (hW : RadialGood W) (hu : 0 < u) :
    ContinuousOn (cayley ∘ fun r => trace W (u * r)) (Icc 0 1) := by
  have hγ : ContinuousOn (fun r => trace W (u * r)) (Icc 0 1) :=
    hW.2.2.2.1.comp (continuous_const.mul continuous_id).continuousOn
      fun r hr => show (0 : ℝ) ≤ u * r from mul_nonneg hu.le hr.1
  exact continuousOn_cayley.comp hγ fun r hr =>
    ne_neg_I_iff.2 (add_I_ne_zero_of_im_nonneg (trace_mem_Hbar hW (mul_nonneg hu.le hr.1)))

theorem isCompact_cayley_trace (hW : RadialGood W) (hu : 0 < u) :
    IsCompact (cayley '' (trace W '' Icc 0 u)) := by
  rw [trace_image_eq_Icc01 hu, ← image_comp]
  exact isCompact_Icc.image_of_continuousOn (continuousOn_cayley_trace hW hu)

theorem frontier_tipD_subset (hW : RadialGood W) (hu : 0 < u) :
    frontier (tipD W u) ⊆ tipE W u := by
  intro w hw
  rw [(isOpen_tipD hW hu).frontier_eq] at hw
  obtain ⟨hcl, hnot⟩ := hw
  have hcl' : w ∈ closedBall (0 : ℂ) 1 := by
    have := closure_mono (tipD_subset_ball (W := W) (u := u)) hcl
    rwa [closure_ball (0 : ℂ) one_ne_zero] at this
  rcases (mem_closedBall.1 hcl').lt_or_eq with hlt | heq
  · right
    have hwb : w ∈ ball (0 : ℂ) 1 := mem_ball.2 hlt
    have hw1 := ne_one_of_mem_ball hwb
    have hzH : cayleyInv w ∈ H := cayleyInv_mem_H hwb
    have hzK : cayleyInv w ∉ H \ fwdHull W u := fun h => hnot (by rw [tipD_eq]; exact ⟨hwb, h⟩)
    have hcont : ContinuousAt cayleyInv w :=
      continuousOn_cayleyInv.continuousAt (isOpen_compl_singleton.mem_nhds hw1)
    have hzcl : cayleyInv w ∈ closure (H \ fwdHull W u) := by
      refine closure_mono ?_ (hcont.continuousWithinAt.mem_closure_image hcl)
      rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      rwa [cayleyInv_cayley (add_I_ne_zero_of_im_nonneg (le_of_lt
        (show (0 : ℝ) < z.im from hz.1)))]
    have hfr : cayleyInv w ∈ frontier (H \ fwdHull W u) := by
      rw [(FwdHolo.isOpen_compl_fwdHull hW.1 hu.le).frontier_eq]
      exact ⟨hzcl, hzK⟩
    have hzA := frontier_compl_fwdHull_inter_H_subset hW.1 hW.2.1 hu.le
      (tendstoUniformlyOn_trace hW u) (hW.2.2.2.1.mono Icc_subset_Ici_self) ⟨hfr, hzH⟩
    exact ⟨cayleyInv w, hzA, cayley_cayleyInv hw1⟩
  · left
    exact mem_sphere.2 heq

theorem tipE_subset_compl (hW : RadialGood W) : tipE W u ⊆ (tipD W u)ᶜ := by
  rintro w hwE ⟨z, hz, rfl⟩
  rcases hwE with hs | ⟨p, ⟨s, hs, rfl⟩, hpz⟩
  · have h1 := cayley_mem_ball hz.1
    rw [mem_sphere] at hs
    rw [mem_ball] at h1
    linarith
  · have hpH := trace_mem_Hbar hW hs.1
    have hpz' := bijOn_cayley_Hbar.injOn hpH (H_subset_Hbar hz.1) hpz
    have hK := trace_mem_fwdHull_of_mem_H hW hs.1 hs.2 (hpz' ▸ hz.1)
    exact hz.2 (hpz' ▸ hK)

/-- `ψ = cayley ∘ f̂_u` satisfies EXT-CA's standing hypotheses `(Hψ)`. -/
theorem carHyp_tip (hW : RadialGood W) (hu : 0 < u) :
    CarHyp (cayley ∘ fwdMapInv W u) (tipD W u) (tipE W u) 2 where
  holo := differentiableOn_cayley_Hbar.comp
    (fun z hz => (differentiableAt_fwdMapInv hW.1 hW.2.1 hu.le hz).differentiableWithinAt)
    fun z hz => H_subset_Hbar (fwdMapInv_mem_H hW.1 hW.2.1 hu.le hz)
  bij := by
    have h1 : BijOn (fwdMapInv W u) H (H \ fwdHull W u) := by
      rw [← image_fwdMapInv_H hW.1 hW.2.1 hu.le]
      exact (injOn_fwdMapInv_H hW.1 hW.2.1 hu.le).bijOn_image
    exact (bijOn_cayley_Hbar.injOn.mono fun z hz => H_subset_Hbar hz.1).bijOn_image.comp h1
  isOpen := isOpen_tipD hW hu
  bdd := fun w hw => by
    have := tipD_subset_ball hw
    rw [mem_ball] at this ⊢
    linarith
  isClosed := isClosed_sphere.union (isCompact_cayley_trace hW hu).isClosed
  frontier_sub := frontier_tipD_subset hW hu
  sub_compl := tipE_subset_compl hW
  E_bdd := by
    rintro w (hs | ⟨p, ⟨s, hs, rfl⟩, rfl⟩)
    · rw [mem_sphere] at hs
      rw [mem_closedBall]
      linarith
    · have := cayley_mem_closedBall (trace_mem_Hbar hW hs.1)
      rw [mem_closedBall] at this ⊢
      linarith

theorem ulc_tipE (hW : RadialGood W) (hu : 0 < u) : ULC (tipE W u) := by
  have hc := continuousOn_cayley_trace hW hu
  have := ULC.union_of_isCompact_of_isClosed (isCompact_sphere (0 : ℂ) 1)
    (isCompact_Icc.image_of_continuousOn hc).isClosed (ULC.sphere 0 1) (ULC.image_Icc hc)
  rwa [image_comp, ← trace_image_eq_Icc01 hu] at this

/-- **TIP-b, deterministic core.** For a driver with the TR4 conclusion and `u > 0`,
`f̂_u(w) → η u` as `w → 0` in `ℍ` (Carathéodory's continuity theorem, EXT-CA C3, with GEN-b). -/
theorem tendsto_fwdMapInv_nhdsWithin_H_zero (hW : RadialGood W) (hu : 0 < u) :
    Tendsto (fwdMapInv W u) (𝓝[H] 0) (𝓝 (trace W u)) := by
  obtain ⟨F, hFeq, hFc, -, -⟩ := continuousOn_extension (carHyp_tip hW hu) (ulc_tipE hW hu)
  have h0 : (0 : ℂ) ∈ Hbar := by show (0 : ℝ) ≤ (0 : ℂ).im; simp
  have hlim := tendsto_nhdsWithin_H_of_extension hFeq hFc h0
  have hηI : trace W u + I ≠ 0 := add_I_ne_zero_of_im_nonneg (trace_mem_Hbar hW hu.le)
  have hcay : ContinuousAt cayley (trace W u) :=
    continuousOn_cayley.continuousAt
      (isOpen_compl_singleton.mem_nhds (show trace W u ∉ ({-I} : Set ℂ) from
        fun h => ne_neg_I_iff.2 hηI h))
  have hrad : Tendsto (fun y : ℝ => (cayley ∘ fwdMapInv W u) ((y : ℂ) * I)) (𝓝[>] 0)
      (𝓝 (cayley (trace W u))) := hcay.tendsto.comp (hW.tendsto hu.le)
  have hiy : Tendsto (fun y : ℝ => (y : ℂ) * I) (𝓝[>] 0) (𝓝[H] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_ofReal_mul_I_nhdsGT_zero,
      eventually_mem_nhdsWithin.mono fun y hy => mul_I_mem_H hy⟩
  have hF0 : F 0 = cayley (trace W u) := tendsto_nhds_unique (hlim.comp hiy) hrad
  rw [hF0] at hlim
  have hc1 : cayley (trace W u) ≠ 1 := cayley_ne_one hηI
  have hinv : ContinuousAt cayleyInv (cayley (trace W u)) :=
    continuousOn_cayleyInv.continuousAt (isOpen_compl_singleton.mem_nhds hc1)
  have h2 := hinv.tendsto.comp hlim
  rw [cayleyInv_cayley hηI] at h2
  refine h2.congr' (eventually_mem_nhdsWithin.mono fun w hw => ?_)
  exact cayleyInv_cayley (add_I_ne_zero_of_im_nonneg
    (le_of_lt (fwdMapInv_mem_H hW.1 hW.2.1 hu.le hw)))

/-! ## TIP, SIM and HULL for `κ ≤ 4` -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **TIP (EXT-RS), all `0 < κ ≤ 4`.** Almost surely the SLE trace never returns to `0` at a
positive time. RS Thm 6.1 (p. 23). -/
theorem ae_sleTrace_ne_zero [IsProbabilityMeasure P] (hB : IsBrownianReal B P) {κ : ℝ}
    (hκ : 0 < κ) (hκ4 : κ ≤ 4) :
    ∀ᵐ ω ∂P, ∀ t > (0 : ℝ), sleTrace κ B ω t ≠ 0 := by
  have hq : ∀ q : ℚ, ∀ᵐ ω ∂P, 0 < (q : ℝ) →
      RadialGood (shiftDrive (drive κ B ω) q) ∧ NoRealHitDet (shiftDrive (drive κ B ω) q) := by
    intro q
    filter_upwards [ae_shift_good hB hκ hκ4 (q : ℝ).toNNReal] with ω hs hq0
    rwa [Real.coe_toNNReal _ hq0.le] at hs
  filter_upwards [ae_radialGood_drive hB hκ (by linarith), ae_all_iff.2 hq] with ω hg hqω
  intro t ht
  refine trace_ne_zero_of_dense hg Rat.denseRange_cast (fun v hv hv0 => ?_) ht
  obtain ⟨q, rfl⟩ := hv
  exact ⟨(hqω q hv0).1, (hqω q hv0).2, tendsto_fwdMapInv_nhdsWithin_H_zero hg hv0⟩

/-- **SIM (EXT-RS), all `0 < κ ≤ 4`.** RS Thm 6.1 (p. 23). -/
theorem ae_sleTrace_simple_of_le_four [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) :
    ∀ᵐ ω ∂P, InjOn (sleTrace κ B ω) (Ici 0) ∧ ∀ t > (0 : ℝ), sleTrace κ B ω t ∈ H :=
  ae_sleTrace_simple hB hκ hκ4 fun _ hB' => ae_sleTrace_ne_zero hB' hκ hκ4

/-- **HULL (EXT-RS), all `0 < κ ≤ 4`.** RS Thm 6.1 (p. 23), Exercise 6.7 (p. 30). -/
theorem ae_fwdHull_eq_sleTrace_image_of_le_four [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → fwdHull (drive κ B ω) t = sleTrace κ B ω '' Ioc 0 t :=
  ae_fwdHull_eq_sleTrace_image hB hκ hκ4 fun _ hB' => ae_sleTrace_ne_zero hB' hκ hκ4

end RS
end QuantumZipper
