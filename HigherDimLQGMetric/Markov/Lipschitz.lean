import HigherDimLQGMetric.Markov.Kernel
import HigherDimLQGMetric.LogEnergy.DecaySlice
import HigherDimLQGMetric.LogEnergy.QuantDeriv

/-! Local regularity of the exterior point Riesz vectors. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Set Metric TopologicalSpace Filter
open HigherDimLFPP (Rd)
open scoped RealInnerProductSpace
open scoped Topology

namespace HigherDimLQGMetric

variable {d : ℕ}

/-- The two-variable logarithmic kernel with a cutoff in its second variable. -/
def markovJointCutLog (χ : Rd d → ℝ) (p : Rd d × Rd d) : ℝ :=
  χ p.2 * (-Real.log ‖p.1 - p.2‖)

theorem markov_jointCutLog_contDiffAt (x₀ : Rd d) {χ : Rd d → ℝ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    {ε : ℝ} (hε : 0 < ε) (hχ0 : ∀ y ∈ ball x₀ ε, χ y = 0)
    {p : Rd d × Rd d} (hp : p.1 ∈ ball x₀ (ε / 4)) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (markovJointCutLog χ) p := by
  by_cases hdiag : p.1 = p.2
  · have hp2 : p.2 ∈ ball x₀ ε := by
      rw [← hdiag]
      exact ball_subset_ball (by linarith) hp
    have heq : markovJointCutLog χ =ᶠ[𝓝 p] (fun _ => (0 : ℝ)) := by
      have hball : (Prod.snd ⁻¹' ball x₀ ε : Set (Rd d × Rd d)) ∈ 𝓝 p :=
        (isOpen_ball.preimage continuous_snd).mem_nhds hp2
      filter_upwards [hball] with q hq
      simp [markovJointCutLog, hχ0 q.2 hq]
    exact contDiffAt_const.congr_of_eventuallyEq heq
  · have hsub : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : Rd d × Rd d => q.1 - q.2) p := by fun_prop
    have hne : p.1 - p.2 ≠ 0 := sub_ne_zero.mpr hdiag
    have hlog : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : Rd d × Rd d => Real.log ‖q.1 - q.2‖) p :=
      (hsub.norm ℝ hne).log (norm_ne_zero_iff.mpr hne)
    exact ((hχ.contDiffAt.comp p contDiffAt_snd).mul hlog.neg)

/-- A parameterized smooth kernel is locally Lipschitz in every spatial derivative when
restricted to a compact product. -/
theorem markov_slice_deriv_diff_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E × F → ℝ) (Kx : Set E) (Ku : Set F)
    (hKx : IsCompact Kx) (hKu : IsCompact Ku) (hKconv : Convex ℝ Kx)
    (hf : ∀ p ∈ Kx ×ˢ Ku, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f p)
    (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Kx, ∀ x' ∈ Kx, ∀ u ∈ Ku,
      ‖iteratedFDeriv ℝ n (fun v : F => f (x',v) - f (x,v)) u‖ ≤
        C * ‖x' - x‖ := by
  obtain ⟨C, hC, hbound⟩ := compact_iteratedFDeriv_lipschitz f n
    (Kx ×ˢ Ku) (hKx.prod hKu) hf
  refine ⟨C, hC, ?_⟩
  intro x hx x' hx' u hu
  have hseg : segment ℝ (x,u) (x',u) ⊆ Kx ×ˢ Ku := by
    have hconv : Convex ℝ (Kx ×ˢ ({u} : Set F)) :=
      hKconv.prod (convex_singleton u)
    intro p hp
    have hp' := hconv.segment_subset
      (show (x,u) ∈ Kx ×ˢ ({u} : Set F) from ⟨hx, mem_singleton u⟩)
      (show (x',u) ∈ Kx ×ˢ ({u} : Set F) from ⟨hx', mem_singleton u⟩) hp
    exact ⟨hp'.1, hp'.2 ▸ hu⟩
  have hnorm : ‖(x',u) - (x,u)‖ = ‖x' - x‖ := by
    simp [Prod.norm_def]
  have hfull := hbound (x,u) (x',u) hseg
  rw [hnorm] at hfull
  let g : F →L[ℝ] (E × F) :=
    (LinearIsometry.inr ℝ E F).toContinuousLinearMap
  have hg (v : E) (hv : v ∈ Kx) :
      iteratedFDeriv ℝ n (fun w : F => f (v,w)) u =
        (iteratedFDeriv ℝ n f (v,u)).compContinuousLinearMap (fun _ => g) := by
    have h := iteratedFDeriv_comp_affine_local f g (v, (0:F)) u n
      (by simpa [g] using hf (v,u) ⟨hv,hu⟩)
    simpa [g] using h
  have hsub :
      (iteratedFDeriv ℝ n f (x',u)).compContinuousLinearMap (fun _ => g) -
      (iteratedFDeriv ℝ n f (x,u)).compContinuousLinearMap (fun _ => g) =
      (iteratedFDeriv ℝ n f (x',u) -
        iteratedFDeriv ℝ n f (x,u)).compContinuousLinearMap (fun _ => g) := by
    ext v
    simp [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hnormcomp := ContinuousMultilinearMap.norm_compContinuous_linearIsometry_le
    (iteratedFDeriv ℝ n f (x',u) - iteratedFDeriv ℝ n f (x,u))
    (fun _ => LinearIsometry.inr ℝ E F)
  have hsmooth (v : E) (hv : v ∈ Kx) :
      ContDiffAt ℝ n (fun w : F => f (v,w)) u := by
    have hmap : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun w : F => (v,w)) u := by fun_prop
    exact ((hf (v,u) ⟨hv,hu⟩).comp u hmap).of_le (by simp)
  have hderiv := iteratedFDeriv_sub_apply (hsmooth x' hx') (hsmooth x hx)
  change iteratedFDeriv ℝ n (fun v : F => f (x',v) - f (x,v)) u = _ at hderiv
  calc
    ‖iteratedFDeriv ℝ n (fun v : F => f (x',v) - f (x,v)) u‖ =
        ‖(iteratedFDeriv ℝ n f (x',u) -
          iteratedFDeriv ℝ n f (x,u)).compContinuousLinearMap (fun _ => g)‖ := by
      rw [hderiv, hg x' hx', hg x hx, hsub]
    _ ≤ ‖iteratedFDeriv ℝ n f (x',u) - iteratedFDeriv ℝ n f (x,u)‖ := by
      simpa [g] using hnormcomp
    _ ≤ C * ‖x' - x‖ := hfull

/-- The exterior logarithmic kernel varies Lipschitz-continuously in the Cameron–Martin norm,
uniformly on a small ball separated from the interior cutoff. -/
theorem markov_cutLog_diff_isCMBounded (hd : 1 ≤ d) (x₀ : Rd d)
    {χ : Rd d → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχc : HasCompactSupport χ) {ε : ℝ} (hε : 0 < ε)
    (hχ0 : ∀ y ∈ ball x₀ ε, χ y = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ closedBall x₀ (ε / 8),
      ∀ x' ∈ closedBall x₀ (ε / 8),
      IsCMBounded (fun y : Rd d => markovJointCutLog χ (x',y) -
        markovJointCutLog χ (x,y)) (C * ‖x' - x‖) := by
  obtain ⟨R, hR, hχR⟩ := hχc.isBounded.exists_pos_norm_lt
  let Kx : Set (Rd d) := closedBall x₀ (ε / 8)
  let Ku : Set (Rd d) := closedBall 0 R
  let f : Rd d × Rd d → ℝ := markovJointCutLog χ
  have hχKu : tsupport χ ⊆ Ku := by
    intro y hy
    have := hχR y hy
    simpa only [Ku, mem_closedBall, dist_zero_right] using le_of_lt this
  have hsm (x : Rd d) (hx : x ∈ Kx) :
      ∀ y : Rd d, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (x,y) := by
    intro y
    apply markov_jointCutLog_contDiffAt x₀ hχ hε hχ0
    change dist x x₀ < ε / 4
    have hx' : dist x x₀ ≤ ε / 8 := hx
    linarith
  have hS : ∀ p ∈ Kx ×ˢ Ku,
      ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f p := by
    intro p hp
    exact hsm p.1 hp.1 p.2
  have hKx : IsCompact Kx := isCompact_closedBall _ _
  have hKu : IsCompact Ku := isCompact_closedBall _ _
  obtain ⟨C₀, hC₀, h0⟩ := markov_slice_deriv_diff_bound f Kx Ku
    hKx hKu (convex_closedBall _ _) hS 0
  obtain ⟨Cₙ, hCₙ, hn⟩ := markov_slice_deriv_diff_bound f Kx Ku
    hKx hKu (convex_closedBall _ _) hS (2*(d/2+1))
  obtain ⟨Ccm, hCcm, hCM⟩ := exists_isCMBounded_quantDeriv hd Ku
    measurableSet_closedBall (isCompact_closedBall 0 R).measure_lt_top.ne
  let B : ℝ := 1 + max C₀ Cₙ
  have hB : 0 < B := by
    dsimp [B]
    linarith [le_max_left C₀ Cₙ]
  let C : ℝ := Ccm * B
  refine ⟨C, mul_pos hCcm hB, ?_⟩
  intro x hx x' hx'
  let F : Rd d → ℝ := fun y => f (x',y) - f (x,y)
  have hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F := by
    have hs (v : Rd d) (hv : v ∈ Kx) :
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : Rd d => f (v,y)) := by
      rw [contDiff_iff_contDiffAt]
      intro y
      have hmap : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun w : Rd d => (v,w)) y := by fun_prop
      exact (hsm v hv y).comp y hmap
    exact (hs x' hx').sub (hs x hx)
  have hFsup : tsupport F ⊆ Ku := by
    have hs (v : Rd d) : tsupport (fun y : Rd d => f (v,y)) ⊆ Ku := by
      exact (tsupport_mul_subset_left).trans hχKu
    exact (tsupport_sub _ _).trans (union_subset (hs x') (hs x))
  have hFc : HasCompactSupport F :=
    hKu.of_isClosed_subset (isClosed_tsupport _) hFsup
  have hM : 0 ≤ B * ‖x' - x‖ := mul_nonneg hB.le (norm_nonneg _)
  have hbd (n : ℕ) (A : ℝ) (hA : A ≤ B)
      (hb : ∀ u ∈ Ku, ‖iteratedFDeriv ℝ n F u‖ ≤ A * ‖x' - x‖) :
      ∀ u, ‖iteratedFDeriv ℝ n F u‖ ≤ B * ‖x' - x‖ := by
    intro u
    by_cases hu : u ∈ Ku
    · exact (hb u hu).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
    · have hts : u ∉ tsupport F := fun ht => hu (hFsup ht)
      have hz : iteratedFDeriv ℝ n F u = 0 := by
        by_contra hne
        exact hts (support_iteratedFDeriv_subset n
          (by simpa [Function.mem_support] using hne))
      rw [hz, norm_zero]
      exact hM
  have hzero : ∀ u, |F u| ≤ B * ‖x' - x‖ := by
    intro u
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using
      (hbd 0 C₀ (by dsimp [B]; linarith [le_max_left C₀ Cₙ])
        (fun u hu => h0 x hx x' hx' u hu) u)
  have hderiv : ∀ u, ‖iteratedFDeriv ℝ (2*(d/2+1)) F u‖ ≤
      B * ‖x' - x‖ :=
    hbd _ Cₙ (by dsimp [B]; linarith [le_max_right C₀ Cₙ])
      (fun u hu => hn x hx x' hx' u hu)
  have hbase := hCM hF hFc hFsup hM hzero hderiv
  simpa [C, B, F, f, mul_assoc] using hbase

theorem markov_cutKernel_contDiff_local (hd : 1 ≤ d) (ρ : TestRd d)
    (x₀ : Rd d) {χ : Rd d → ℝ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    {ε : ℝ} (hε : 0 < ε) (hχ0 : ∀ y ∈ ball x₀ ε, χ y = 0)
    {x : Rd d} (hx : x ∈ closedBall x₀ (ε / 8)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (markovCutKernel ρ χ x) := by
  have hzero : ∀ y ∈ ball x (ε / 4), χ y = 0 := by
    intro y hy
    apply hχ0
    have hxx : dist x x₀ ≤ ε / 8 := hx
    have hxy : dist y x < ε / 4 := hy
    change dist y x₀ < ε
    calc
      dist y x₀ ≤ dist y x + dist x x₀ := dist_triangle _ _ _
      _ < ε := by linarith
  exact markov_contDiff_cutKernel hd ρ x hχ ⟨ε / 4, by positivity, hzero⟩

/-- Integral form of the point-vector covariance using a common cutoff. -/
theorem markovPointVec_inner_cutKernel {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hd : 1 ≤ d) (hh : IsWholeSpaceLGF h P)
    (V : Opens (Rd d)) (hVb : Bornology.IsBounded (V : Set (Rd d)))
    {ρ : TestRd d} (hρ : ∫ y, ρ y = 1)
    (hρV : tsupport (ρ : Rd d → ℝ) ⊆ V)
    (χ : Rd d → ℝ) (hχV : ∀ y ∈ closure (V : Set (Rd d)), χ y = 1)
    (x : Rd d) (hx : x ∈ extOpen V) (φ : TestOn V) :
    ⟪markovPointVec hd hh V hVb hρ hρV x hx,
      markovInsideVec hh V hρ φ⟫ =
      ∫ y, markovCutKernel ρ χ x y * (markovInsideTest V hρ φ).1 y := by
  rw [markovPointVec_inner]
  apply integral_congr_ae
  refine ae_of_all _ fun y => ?_
  by_cases hy : y ∈ V
  · have hχy : χ y = 1 := hχV y (subset_closure hy)
    simp [markovCutKernel, hχy]
  · have hy0 : (markovInsideTest V hρ φ).1 y = 0 :=
      image_eq_zero_of_notMem_tsupport
        (fun ht => hy (markov_insideTest_tsupport V hρ hρV φ ht))
    simp [hy0]

/-- Local Lipschitz continuity of the exterior point vectors in the Gaussian Hilbert space. -/
theorem markovPointVec_local_lipschitz {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hd : 1 ≤ d) (hh : IsWholeSpaceLGF h P)
    (V : Opens (Rd d)) (hVb : Bornology.IsBounded (V : Set (Rd d)))
    {ρ : TestRd d} (hρ : ∫ y, ρ y = 1)
    (hρV : tsupport (ρ : Rd d → ℝ) ⊆ V)
    (x₀ : Rd d) (hx₀ : x₀ ∈ extOpen V) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ball x₀ ε ⊆ extOpen V ∧
      ∀ x (hx : x ∈ extOpen V), ∀ x' (hx' : x' ∈ extOpen V),
        x ∈ closedBall x₀ ε → x' ∈ closedBall x₀ ε →
          ‖markovPointVec hd hh V hVb hρ hρV x' hx' -
            markovPointVec hd hh V hVb hρ hρV x hx‖ ≤ C * ‖x' - x‖ := by
  obtain ⟨χ, hχ, hχc, hχV, ε₀, hε₀, hχ0⟩ := markov_exists_cutoff V hVb hx₀
  obtain ⟨C, hC, hCM⟩ := markov_cutLog_diff_isCMBounded hd x₀ hχ hχc hε₀ hχ0
  refine ⟨ε₀ / 8, C, by positivity, hC, ?_, ?_⟩
  · intro y hy hcl
    have hy' : y ∈ ball x₀ ε₀ := ball_subset_ball (by linarith) hy
    have h1 := hχV y hcl
    have h0 := hχ0 y hy'
    linarith
  intro x hx x' hx' hxb hx'b
  let f : Rd d → ℝ := fun y => markovJointCutLog χ (x',y) - markovJointCutLog χ (x,y)
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f := by
    have hfx : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : Rd d => markovJointCutLog χ (x,y)) := by
      rw [contDiff_iff_contDiffAt]
      intro y
      have hmap : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun w : Rd d => (x,w)) y := by fun_prop
      have hxx : x ∈ ball x₀ (ε₀ / 4) := by
        have hxb' : dist x x₀ ≤ ε₀ / 8 := hxb
        exact lt_of_le_of_lt hxb' (by linarith)
      exact (markov_jointCutLog_contDiffAt (p := (x,y)) x₀ hχ hε₀ hχ0 hxx).comp y hmap
    have hfx' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : Rd d => markovJointCutLog χ (x',y)) := by
      rw [contDiff_iff_contDiffAt]
      intro y
      have hmap : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun w : Rd d => (x',w)) y := by fun_prop
      have hxx' : x' ∈ ball x₀ (ε₀ / 4) := by
        have hxb' : dist x' x₀ ≤ ε₀ / 8 := hx'b
        exact lt_of_le_of_lt hxb' (by linarith)
      exact (markov_jointCutLog_contDiffAt (p := (x',y)) x₀ hχ hε₀ hχ0 hxx').comp y hmap
    exact hfx'.sub hfx
  let F : C(Rd d, ℝ) := ⟨f, hf.continuous⟩
  obtain ⟨Y, hYmem, hYnorm, hYinner⟩ :=
    markov_exists_projected_cmVec hh V hρ F (hCM x hxb x' hx'b)
  let D : Lp ℝ 2 P := markovPointVec hd hh V hVb hρ hρV x' hx' -
    markovPointVec hd hh V hVb hρ hρV x hx
  have hDmem : D ∈ markovInsideSpace hh V hρ :=
    Submodule.sub_mem _ (markovPointVec_mem hd hh V hVb hρ hρV x' hx')
      (markovPointVec_mem hd hh V hVb hρ hρV x hx)
  have hinner (φ : TestOn V) :
      ⟪D, markovInsideVec hh V hρ φ⟫ =
        ⟪Y, markovInsideVec hh V hρ φ⟫ := by
    let t : Rd d → ℝ := (markovInsideTest V hρ φ).1
    have ht : Continuous t := (markovInsideTest V hρ φ).1.continuous
    have htc : HasCompactSupport t := (markovInsideTest V hρ φ).1.hasCompactSupport
    have hi (v : Rd d) (hv : v ∈ closedBall x₀ (ε₀ / 8)) :
        Integrable (fun y => markovCutKernel ρ χ v y * t y) :=
      ((markov_cutKernel_contDiff_local hd ρ x₀ hχ hε₀ hχ0 hv).continuous.mul ht)
        |>.integrable_of_hasCompactSupport htc.mul_left
    rw [show D = markovPointVec hd hh V hVb hρ hρV x' hx' -
      markovPointVec hd hh V hVb hρ hρV x hx from rfl, inner_sub_left,
      markovPointVec_inner_cutKernel hd hh V hVb hρ hρV χ hχV x' hx' φ,
      markovPointVec_inner_cutKernel hd hh V hVb hρ hρV χ hχV x hx φ,
      ← integral_sub (hi x' hx'b) (hi x hxb), hYinner]
    apply integral_congr_ae
    refine ae_of_all _ fun y => ?_
    change (χ y * (-Real.log ‖x' - y‖ - markovLogPot ρ y)) * t y -
      (χ y * (-Real.log ‖x - y‖ - markovLogPot ρ y)) * t y =
      (χ y * (-Real.log ‖x' - y‖) - χ y * (-Real.log ‖x - y‖)) * t y
    ring
  have hDY : D = Y := markov_insideVec_ext hh V hρ hDmem hYmem hinner
  change ‖D‖ ≤ C * ‖x' - x‖
  rw [hDY]
  simpa [abs_of_nonneg (mul_nonneg hC.le (norm_nonneg _))] using hYnorm

end HigherDimLQGMetric
