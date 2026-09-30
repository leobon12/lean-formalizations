import QuantumZipper.Proofs.Section5.Prop16LitMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, literal form: the finiteness node

`Prop16Lit.prop16LitFinStmt_holds`: under the weighted law, the straight local area of
`B(0,t) ∩ ℍ` is finite for some `t > 0`, uniformly in the level `C`. Deterministic core
`fin_point`: for a locally nice sample (`IsLocNiceOn`: agreeing near `D ∪ (a,b)` with a good
sample `y` of finite area on bounded sets plus a continuous function) the local area measure of
the zoomed field is `e^{γφ}·(μ_{y(·+t)}|_U)` (`qAreaMeasureOn_eq_withDensity_of_agree`), with `φ`
bounded on a compact half-disc around the zoom point inside `D ∪ (a,b)`. Local niceness holds
almost surely (`prop16LocNiceStmt_of_coupling`, domain Markov coupling). Own elementary argument.
-/

noncomputable section

open Filter Set Metric MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Lit

open Prop16Asm Prop16Area.G

/-- **Finite local area near the zoom point, one sample.** -/
theorem fin_point {γ : ℝ} (hγ : 0 < γ) {D : Set ℂ} (hD : IsOpen D) (hDH : D ⊆ H) {a b c d : ℝ}
    (hhd : ∀ t ∈ Ioo c d, ∃ r > 0, ball (t : ℂ) r ∩ H ⊆ D) (hca : c ≤ a) (hbd : b ≤ d)
    {h0 : ℂ → ℝ} (hh0 : ContinuousOn h0 (D ∪ realSet (Ioo a b))) {x0 : FieldSample}
    (hx : IsLocNiceOn γ (D ∪ realSet (Ioo a b)) x0) {t : ℝ} (ht : t ∈ Ioo a b) :
    ∃ r > 0, ∀ C : ℝ,
      qAreaMeasureOn γ (zoomField γ C (ofFun h0 + x0) t) (zoomDomain D t) (ball 0 r ∩ H) < ⊤ := by
  obtain ⟨W, hWo, hWV, y, ψ, hy, hyfin, -, hψ, hag⟩ := hx
  obtain ⟨r₁, hr₁, hr₁D⟩ := hhd t ⟨lt_of_le_of_lt hca ht.1, lt_of_lt_of_le ht.2 hbd⟩
  set r := min r₁ (min (t - a) (b - t)) / 2 with hr
  have hr0 : 0 < r := by
    have : 0 < min (t - a) (b - t) := lt_min (by linarith [ht.1]) (by linarith [ht.2])
    positivity
  have hrr₁ : r < r₁ := by
    have := min_le_left r₁ (min (t - a) (b - t)); rw [hr]; linarith
  have hrab : r < min (t - a) (b - t) := by
    have := min_le_right r₁ (min (t - a) (b - t))
    have : 0 < min (t - a) (b - t) := lt_min (by linarith [ht.1]) (by linarith [ht.2])
    rw [hr]; linarith
  -- the compact half-disc lies in the zoom neighbourhood
  set K := closedBall (0 : ℂ) r ∩ Hbar with hK
  have hKV : K ⊆ zoomNbhd D a b t := by
    rintro u ⟨hu, huH⟩
    rw [mem_closedBall, dist_zero_right] at hu
    show u + (t : ℂ) ∈ D ∪ realSet (Ioo a b)
    rcases (show (0 : ℝ) ≤ u.im from huH).lt_or_eq with him | him
    · left
      refine hr₁D ⟨?_, ?_⟩
      · rw [mem_ball, dist_eq_norm, add_sub_cancel_right]; linarith
      · show 0 < (u + (t : ℂ)).im
        simpa using him
    · right
      refine ⟨u.re + t, ⟨?_, ?_⟩, ?_⟩
      · have := (abs_le.1 ((Complex.abs_re_le_norm u).trans hu)).1
        have := min_le_left (t - a) (b - t)
        linarith
      · have := (abs_le.1 ((Complex.abs_re_le_norm u).trans hu)).2
        have := min_le_right (t - a) (b - t)
        linarith
      · apply Complex.ext <;> simp [him.symm]
  have hKc : IsCompact K := (isCompact_closedBall _ _).inter_right isClosed_Hbar
  have hψt : ContinuousOn (fun u => ψ (u + t) + h0 (u + t)) (zoomNbhd D a b t) :=
    (continuousOn_comp_add hψ t).add (continuousOn_comp_add hh0 t)
  obtain ⟨Mφ, hMφ⟩ := hKc.exists_bound_of_continuousOn (hψt.mono hKV)
  refine ⟨r, hr0, fun C => ?_⟩
  -- the density representation
  set Wt := (fun z => z + (t : ℂ)) ⁻¹' W with hWt
  have hWto : IsOpen Wt := hWo.preimage (continuous_id.add continuous_const)
  have hWtV : Wt ∩ Hbar = zoomNbhd D a b t := by
    rw [hWt, preimage_add_inter_Hbar, hWV]; rfl
  have hyt : IsLQGGood γ (translate y (t : ℂ)) := hy.translate t
  have hag' := circAgree_ofFun_add hWV hψ hh0 hag
  have hY := fcAgree_zoomField hWo hWV hy (hψ.add hh0) hag' C t
  have hφY : ContinuousOn (fun u => (ψ (u + t) + h0 (u + t)) + C / γ) (Wt ∩ Hbar) := by
    rw [hWtV]; exact hψt.add continuousOn_const
  have hUo : IsOpen (zoomDomain D t) := hD.preimage (continuous_id.add continuous_const)
  have hUH : zoomDomain D t ⊆ H := fun z hz => by
    have : 0 < (z + (t : ℂ)).im := hDH hz
    show 0 < z.im
    simpa using this
  have hUW : zoomDomain D t ⊆ Wt := fun z hz => by
    have : z ∈ zoomNbhd D a b t := preimage_mono subset_union_left hz
    rw [← hWtV] at this
    exact this.1
  rw [qAreaMeasureOn_eq_withDensity_of_agree hWto hyt hφY hY.circAgree hUo hUH hUW]
  have hs : MeasurableSet (ball (0 : ℂ) r ∩ H) :=
    measurableSet_ball.inter (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  rw [withDensity_apply _ hs]
  set M := ENNReal.ofReal (Real.exp (γ * (Mφ + |C / γ|))) with hM
  calc ∫⁻ u in ball 0 r ∩ H, ENNReal.ofReal (Real.exp (γ * ((ψ (u + t) + h0 (u + t)) + C / γ)))
        ∂(qAreaMeasure γ (translate y (t : ℂ))).restrict (zoomDomain D t)
      ≤ ∫⁻ _u in ball 0 r ∩ H, M ∂(qAreaMeasure γ (translate y (t : ℂ))).restrict
          (zoomDomain D t) := by
        refine setLIntegral_mono measurable_const fun u hu => ?_
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
        have huK : u ∈ K := ⟨ball_subset_closedBall hu.1, show (0 : ℝ) ≤ u.im from le_of_lt hu.2⟩
        have h1 : ψ (u + t) + h0 (u + t) ≤ Mφ := by
          have := hMφ u huK
          simp only [Real.norm_eq_abs] at this
          exact (abs_le.1 this).2
        exact mul_le_mul_of_nonneg_left (by linarith [le_abs_self (C / γ)]) hγ.le
    _ = M * (qAreaMeasure γ (translate y (t : ℂ))).restrict (zoomDomain D t) (ball 0 r ∩ H) := by
        rw [setLIntegral_const]
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
        refine (Measure.restrict_apply_le _ _).trans_lt ?_
        rw [GoodTransforms.qAreaMeasure_translate hy t, Measure.map_apply
          (by fun_prop : Measurable fun x : ℂ => x - (t : ℂ)) hs]
        refine (measure_mono ?_).trans_lt (hyfin (|t| + r))
        rintro u ⟨hu, huH⟩
        refine ⟨?_, ?_⟩
        · rw [mem_ball, dist_zero_right] at hu ⊢
          have := norm_sub_norm_le u (t : ℂ)
          rw [Complex.norm_real, Real.norm_eq_abs] at this
          linarith
        · have : 0 < (u - (t : ℂ)).im := huH
          show 0 < u.im
          simpa using this

/-- **The finiteness node holds.** -/
theorem prop16LitFinStmt_holds : Prop16LitFinStmt := by
  intro γ D c d a b h0 Ω _ P X hdat
  have hnice := prop16LocNiceStmt_of_coupling prop16MixedFreeLocCoupling_mm γ D c d a b h0 P X
    hdat
  have hloc := prop16LocGoodStmt_of_coupling prop16MixedFreeLocCoupling_mm
  have hν := prop16NuMeasStmt_of_loc hloc γ D c d a b h0 P X hdat
  obtain ⟨hγ, -, ⟨hDo, -, -, hDH, -, -, hhd⟩, -, hca, hbd, hh0, -, -, -, hfin⟩ := hdat
  exact ae_prop16Law_of_ae (G := fun ω t => ∃ r > 0, ∀ C : ℝ,
      qAreaMeasureOn γ (zoomField γ C (ofFun h0 + X ω) t) (zoomDomain D t) (ball 0 r ∩ H) < ⊤)
    (aemeasurable_prop16Kernel' hν hfin) (fun ω => sFinite_prop16Nu γ h0 a b (X ω))
    (fun ω => prop16Nu_compl_Ioo γ h0 a b (X ω))
    (hnice.mono fun ω hω t ht => fin_point hγ hDo hDH hhd hca hbd hh0 hω ht)

end Prop16Lit

end QuantumZipper
