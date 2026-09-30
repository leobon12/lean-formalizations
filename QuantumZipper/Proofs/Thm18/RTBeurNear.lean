import QuantumZipper.Proofs.Zipper.TipXE0Hcap
import QuantumZipper.Proofs.RS.HullBasics
import QuantumZipper.Proofs.Thm18.LWBeurlingMain
import QuantumZipper.Proofs.Thm18.LWFarDefs3
import QuantumZipper.Proofs.Loewner.CoreArc3b
import QuantumZipper.Proofs.Thm18.ASepHopf
import QuantumZipper.Proofs.Thm18.R18RTMaskNeg
import QuantumZipper.Proofs.Thm18.G1PkgTrace

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT-BEURLING, part 2: Beurling near the curve, small-time comparison, the unzipped curve

Deterministic tools for `PullMassBoundStmt` (`RTBeurMain.lean`).

* `im_fwdMap_le_near`: **Beurling estimate** (Lawler, *Schramm–Loewner evolution*,
  arXiv:0712.3256, Thm 2.10, p. 18; in the harmonic-function form `LWFar.beurlingHarmStmt_holds`,
  Lawler–Werness / Johansson Viklund–Lawler Prop 2.1): for a good chord and `w ∈ H_τ` within `d`
  of `η[0,τ]` and at distance `≥ ρ` from some point of `η[0,τ]`,
  `Im f_τ(w) ≤ (‖w‖ + ρ) C (d/ρ)^{1/2}`. Same proof as `TipXE.im_fwdMap_le_base` (which is the
  case of the base point `0`), with the continuum `η[0,τ]`.
* `im_fwdMap_ge_shift`: over a short time `σ` in which the driver moves little, a point whose
  image `f_s(z)` is at distance `≥ δ` from `0` keeps a fixed fraction of its imaginary part:
  `Im f_{s+σ}(z) ≥ e^{-8σ/δ²} Im f_s(z)` (flow property, `norm_fwdMap_sub_le_uniform`,
  `ASep.im_fwdMap_ge_of_lower`). Own elementary argument.
* `zero_mem_unzCurve`, `fwdMap_trace_mem_unzCurve`: `0` and `f_s(η(t))`, `t > s`, lie on the
  unzipped remaining curve (`tendsto_fwdMapInv_shift`, `RS.trace_scale`).
-/

noncomputable section

open Set Metric Filter
open scoped Topology

namespace QuantumZipper
namespace RTBeur

open Thm18Asm.LWFar

/-- **Beurling estimate near the curve.** -/
theorem im_fwdMap_le_near : ∃ C : ℝ, 0 ≤ C ∧ ∀ (W : ℝ → ℝ), GoodChord W → ∀ τ ρ d : ℝ,
    0 ≤ τ → 0 < d → d ≤ ρ → ∀ w ∈ H \ fwdHull W τ,
    (∃ r ∈ Icc (0 : ℝ) τ, dist w (trace W r) ≤ d) →
    (∃ r ∈ Icc (0 : ℝ) τ, ρ ≤ dist w (trace W r)) →
    (fwdMap W τ w).im ≤ (‖w‖ + ρ) * (C * (d / ρ) ^ (1 / 2 : ℝ)) := by
  obtain ⟨C, hC0, hB⟩ := beurlingHarmStmt_holds
  refine ⟨C, hC0, fun W hW τ ρ d hτ hd hdρ w hw hnear hfar => ?_⟩
  have hWc := hW.cont
  have hρ : 0 < ρ := hd.trans_le hdρ
  set D : Set ℂ := H \ fwdHull W τ with hD
  have hDo : IsOpen D := FwdHolo.isOpen_compl_fwdHull hWc hτ
  set K : Set ℂ := trace W '' Icc 0 τ with hK
  have hKc : IsConnected K :=
    (isConnected_Icc hτ).image _ (hW.simple.2.1.mono Icc_subset_Ici_self)
  have htr0 : trace W 0 = 0 := hW.simple.1
  have hKD : Disjoint K D := by
    rw [Set.disjoint_left]
    rintro _ ⟨r, hr, rfl⟩ hrD
    rcases hr.1.eq_or_lt with h0 | hpos
    · rw [← h0, htr0] at hrD
      have := hrD.1
      simp [H] at this
    · exact hrD.2 (by rw [hW.hull τ hτ]; exact ⟨r, ⟨hpos, hr.2⟩, rfl⟩)
  have hKd : (K ∩ closedBall w d).Nonempty := by
    obtain ⟨r, hr, hr2⟩ := hnear
    exact ⟨trace W r, ⟨r, hr, rfl⟩, by rw [mem_closedBall, dist_comm]; exact hr2⟩
  have hKρ : (K \ ball w ρ).Nonempty := by
    obtain ⟨r, hr, hr2⟩ := hfar
    refine ⟨trace W r, ⟨r, hr, rfl⟩, fun hb => ?_⟩
    rw [mem_ball, dist_comm] at hb
    linarith
  set M : ℝ := ‖w‖ + ρ with hM
  have hMpos : 0 < M := by positivity
  set h : ℂ → ℝ := fun x => (fwdMap W τ x).im / M with hh
  set V := connectedComponentIn (D ∩ ball w ρ) w with hV
  have hVsub : V ⊆ D ∩ ball w ρ := connectedComponentIn_subset _ _
  have hharm : InnerProductSpace.HarmonicOnNhd h V := by
    intro x hx
    have hxD := (hVsub hx).1
    have ha : AnalyticAt ℂ (fwdMap W τ) x :=
      (FwdHolo.differentiableOn_fwdMap hWc hτ).analyticAt (hDo.mem_nhds hxD)
    have := ha.harmonicAt_im.const_smul (c := M⁻¹)
    convert this using 1
    funext y
    simp [hh, div_eq_inv_mul]
  have hbnd : ∀ x ∈ V, 0 ≤ h x ∧ h x ≤ 1 := by
    intro x hx
    obtain ⟨hxD, hxb⟩ := hVsub hx
    have hpos := (RS.im_fwdMap_le_of_le hWc hτ le_rfl hxD).2
    have hle := RS.im_fwdMap_le_im hWc hτ hxD
    have hxn : ‖x‖ ≤ M := by
      rw [mem_ball, dist_eq_norm] at hxb
      have := norm_le_norm_add_norm_sub' x w
      linarith
    refine ⟨div_nonneg hpos.le hMpos.le, (div_le_one hMpos).2 ?_⟩
    linarith [Complex.im_le_norm x]
  have hfr : ∀ x₀ ∈ frontier D ∩ ball w ρ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ V, dist x x₀ < δ → h x ≤ ε := by
    intro x₀ hx₀ ε hε
    have hnot : x₀ ∉ D := fun h' => (hDo.frontier_eq ▸ hx₀.1).2 h'
    have hcl : x₀ ∈ closure D := frontier_subset_closure hx₀.1
    have hclH : closure D ⊆ {z : ℂ | 0 ≤ z.im} :=
      closure_minimal (fun z hz => show 0 ≤ z.im from le_of_lt hz.1)
        (isClosed_le continuous_const Complex.continuous_im)
    have hp : x₀ ∈ fwdHull W τ ∨ x₀.im = 0 := by
      rcases (show (0:ℝ) ≤ x₀.im from hclH hcl).eq_or_lt with h0 | hpos
      · exact Or.inr h0.symm
      · exact Or.inl (by by_contra hK'; exact hnot ⟨hpos, hK'⟩)
    have ht := RS.tendsto_im_fwdMap_hull hWc hτ hp
    rw [Metric.tendsto_nhdsWithin_nhds] at ht
    obtain ⟨δ, hδ, hδ'⟩ := ht (ε * M) (by positivity)
    refine ⟨δ, hδ, fun x hx hxd => ?_⟩
    have := hδ' (hVsub hx).1 hxd
    rw [Real.dist_eq, sub_zero] at this
    have h1 : (fwdMap W τ x).im ≤ ε * M := (le_abs_self _).trans this.le
    show (fwdMap W τ x).im / M ≤ ε
    rw [div_le_iff₀ hMpos]
    linarith
  have hmain := hB D K w d ρ h hDo hw hd hdρ hKc hKD hKd hKρ hharm hbnd hfr
  have e : (fwdMap W τ w).im = M * h w := by
    simp only [hh]; field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left hmain hMpos.le

/-- **Small-time comparison of imaginary parts.** -/
theorem im_fwdMap_ge_shift {W : ℝ → ℝ} (hWc : Continuous W) {s σ δ M : ℝ} (hs : 0 ≤ s)
    (hσ : 0 < σ) (hδ : 0 < δ) (hM : ∀ r ∈ Icc (0 : ℝ) σ, |W (s + r) - W s| ≤ M)
    (hsmall : 24 * M + 8 * Real.sqrt σ ≤ δ / 2) {z : ℂ} (hz : z ∈ H \ fwdHull W (s + σ))
    (hfar : δ ≤ ‖fwdMap W s z‖) :
    (fwdMap W s z).im * Real.exp (-2 * σ / (δ / 2) ^ 2) ≤ (fwdMap W (s + σ) z).im := by
  obtain ⟨hz0, T', hT', u, hu⟩ := (FwdHolo.mem_compl_fwdHull_iff (by linarith)).1 hz
  set V : ℝ → ℝ := fun r => W (s + r) - W s with hVdef
  have hVc : Continuous V := by rw [hVdef]; fun_prop
  have hV0 : V 0 = 0 := by simp [hVdef]
  have hu' : IsForwardSol W z (s + (T' - s)) u := by
    rw [show s + (T' - s) = T' by ring]; exact hu
  have hsh := isForwardSol_shift hu' hs (by linarith)
  have hus : u s = fwdMap W s z := (fwdMap_eq hWc hz0 hu ⟨hs, by linarith⟩).symm
  rw [hus] at hsh
  have hflow := fwdMap_add hWc hz0 hs hσ.le ⟨u, isForwardSol_restrict hu (by linarith) hT'.le⟩
  set u' := fwdMap W s z with hu'def
  have hzs : z ∈ H \ fwdHull W s :=
    (FwdHolo.mem_compl_fwdHull_iff hs).2 ⟨hz0, T', by linarith, u, hu⟩
  have hpos : 0 < u'.im := (RS.im_fwdMap_le_of_le hWc hs le_rfl hzs).2
  have hmemV : ∀ r ∈ Icc (0 : ℝ) σ, u' ∈ H \ fwdHull V r := fun r hr =>
    (FwdHolo.mem_compl_fwdHull_iff hr.1).2 ⟨hpos, T' - s, by linarith [hr.2], _, hsh⟩
  have hlow : ∀ r ∈ Icc (0 : ℝ) σ, δ / 2 ≤ ‖fwdMap V r u'‖ := by
    intro r hr
    rcases hr.1.eq_or_lt with h0 | hr0
    · rw [← h0, TipXE.fwdMap_zero_eq hVc hV0 hσ.le (hmemV σ ⟨hσ.le, le_rfl⟩)]
      linarith
    · have hb := CoreArc.norm_fwdMap_sub_le_uniform hVc hV0 hr0
        (fun t ht => hM t ⟨ht.1, ht.2.trans hr.2⟩) (hmemV r hr)
      have hsq : Real.sqrt r ≤ Real.sqrt σ := Real.sqrt_le_sqrt hr.2
      have := norm_le_norm_add_norm_sub' u' (fwdMap V r u')
      rw [norm_sub_rev] at this
      linarith
  have hge := ASep.im_fwdMap_ge_of_lower hVc hpos (by positivity : 0 < δ / 2)
    ⟨_, isForwardSol_restrict hsh hσ.le (by linarith)⟩ hlow ⟨hσ.le, le_rfl⟩
  rw [hflow]
  exact hge

/-- `0` lies on the unzipped remaining curve. -/
theorem zero_mem_unzCurve {W : ℝ → ℝ} (hWc : Continuous W) (s a : ℝ) :
    (0 : ℂ) ∈ R18.unzCurve W s a := by
  show ((a⁻¹ : ℝ) : ℂ) * 0 ∈ curveOf (R18.outDrv W s a)
  rw [mul_zero]
  have hc : Continuous (R18.outDrv W s a) := by unfold R18.outDrv; fun_prop
  refine subset_closure ⟨0, ?_⟩
  simp only [NNRat.cast_zero]
  rw [Thm18Asm.G1Pkg.trace_zero_time hc]
  simp [R18.outDrv]

/-- The image `f_s(η(t))`, `t > s`, lies on the unzipped remaining curve. -/
theorem fwdMap_trace_mem_unzCurve {W : ℝ → ℝ} (hRG : RS.RadialGood W)
    (hsc : IsSimpleChord (trace W)) (hhull : ∀ t : ℝ, 0 ≤ t → fwdHull W t = trace W '' Ioc 0 t)
    {s a t : ℝ} (hs : 0 ≤ s) (ha : 0 < a) (hst : s < t) :
    fwdMap W s (trace W t) ∈ R18.unzCurve W s a := by
  have hWc := hRG.1
  set Vs : ℝ → ℝ := fun r => RS.shiftDrive W s (a ^ 2 * r) / a with hVs
  have hcong : curveOf (R18.outDrv W s a) = curveOf Vs := R18.curveOf_congr fun u hu => by
    simp only [R18.outDrv, hVs, RS.shiftDrive, max_eq_left hu]
    rw [max_eq_left (by positivity)]
  have hVc : Continuous (RS.shiftDrive W s) := RS.continuous_shiftDrive hWc s
  have hV0 : RS.shiftDrive W s 0 = 0 := by simp [RS.shiftDrive]
  have htrq : ∀ x : ℝ, 0 < x → trace Vs x = fwdMap W s (trace W (s + a ^ 2 * x)) / a := by
    intro x hx
    have hp := R18.tendsto_fwdMapInv_shift hRG hsc.2.2.1 hsc.2.2.2.1 (hhull s hs) hs
      (u := a ^ 2 * x) (by positivity)
    rw [if_neg (by positivity : (0 : ℝ) < a ^ 2 * x).ne'] at hp
    have e : trace (RS.shiftDrive W s) (a ^ 2 * x) = fwdMap W s (trace W (s + a ^ 2 * x)) :=
      hp.limUnder_eq
    rw [← e]
    exact (RS.trace_scale hVc hV0 ha hx.le hp).2
  set g : ℝ → ℂ := fun x => fwdMap W s (trace W (s + a ^ 2 * x)) / a with hg
  set x₀ : ℝ := (t - s) / a ^ 2 with hx₀def
  have hx₀ : 0 < x₀ := div_pos (by linarith) (by positivity)
  have hsx : s + a ^ 2 * x₀ = t := by rw [hx₀def]; field_simp; ring
  have htH : trace W t ∈ H \ fwdHull W s := by
    refine ⟨hsc.2.2.2.1 t (by linarith), ?_⟩
    rw [hhull s hs]
    rintro ⟨r, hr, hrt⟩
    have := hsc.2.2.1 (mem_Ici.2 hr.1.le) (mem_Ici.2 (by linarith)) hrt
    linarith [hr.2]
  have hgc : ContinuousAt g x₀ := by
    have h1 : ContinuousAt (fun x : ℝ => s + a ^ 2 * x) x₀ := by fun_prop
    have h2 : ContinuousAt (trace W) (s + a ^ 2 * x₀) := by
      rw [hsx]; exact hsc.2.1.continuousAt (Ici_mem_nhds (by linarith))
    have h3 : ContinuousAt (fwdMap W s) (trace W (s + a ^ 2 * x₀)) := by
      rw [hsx]; exact RS.continuousAt_fwdMap_of_mem_complHull hWc hs htH
    have h21 : ContinuousAt (fun x : ℝ => trace W (s + a ^ 2 * x)) x₀ :=
      ContinuousAt.comp (f := fun x : ℝ => s + a ^ 2 * x) h2 h1
    have h321 : ContinuousAt (fun x : ℝ => fwdMap W s (trace W (s + a ^ 2 * x))) x₀ :=
      ContinuousAt.comp (f := fun x : ℝ => trace W (s + a ^ 2 * x)) h3 h21
    exact h321.div_const _
  show ((a⁻¹ : ℝ) : ℂ) * fwdMap W s (trace W t) ∈ curveOf (R18.outDrv W s a)
  rw [hcong]
  have hval : ((a⁻¹ : ℝ) : ℂ) * fwdMap W s (trace W t) = g x₀ := by
    simp only [hg, hsx]; rw [Complex.ofReal_inv, div_eq_inv_mul]
  rw [hval]
  unfold curveOf
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδg⟩ := Metric.continuousAt_iff.1 hgc ε hε
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_add_of_pos_right x₀ hδ)
  have hq0 : (0 : ℝ) < q := hx₀.trans hq1
  have hq0' : (0 : ℚ) ≤ q := by exact_mod_cast hq0.le
  refine ⟨trace Vs (q : ℝ), ⟨q.toNNRat, ?_⟩, ?_⟩
  · have hc : ((q.toNNRat : ℚ≥0) : ℝ) = (q : ℝ) := by
      exact_mod_cast congrArg (fun x : ℚ => (x : ℝ)) (Rat.coe_toNNRat q hq0')
    show trace Vs ((q.toNNRat : ℚ≥0) : ℝ) = trace Vs (q : ℝ)
    rw [hc]
  · rw [htrq q hq0, dist_comm]
    exact hδg (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)

end RTBeur
end QuantumZipper
