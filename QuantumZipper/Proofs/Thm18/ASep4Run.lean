import QuantumZipper.Proofs.Thm18.ASep4Raw

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP4 (step 7): the scale engine run on one rational box

On a rational box `S` of scaled good parameters `q = (τ, a, s)` (`ScaleGood`), almost surely, for
every `q ∈ S`, the unzipped rescaled field `x_q = coordChange (rescale X Q s) f_τ⁻¹ Q`
(`xS`) satisfies (`ae_scale_run_box`):
* the continuous-radius limit `lim_{ρ → 0⁺} ∫ evalReg x_q (fc(v, ρ)) dν_q(v)` exists (the input of
  conjunct 1, scale version of `ae_tendsto_Phi_box`);
* the dyadic pairings converge to the raw value: `∫ avgReg x_q j dν_q → x_q(ν_q)` (the input of
  conjunct 2, scale version of `ae_tendsto_free_box`).

Engine: `GenUC.ae_unifConv_all_radii` for the dilated family `genFam_scaleBox`, identity
`ae_ident_scale`, deterministic part `det_unif_A0_rho`, joint continuity `continuousOn_Phi_scale`;
the limit is identified with the raw value by `ae_raw_scale`, `continuousOn_raw_scale` and
density. Source: Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1 (through the engine);
own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology

namespace QuantumZipper
namespace ASep

open Thm18Asm Thm18Asm.G4Core RegCont GenUC CoordReg

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- The unzipped rescaled field at the scaled parameter `q = (τ, a, s)`. -/
def xS (X : Ω → FieldSample) (W : ℝ → ℝ) (Q : ℝ) (q : Fin 3 → ℝ) (ω : Ω) : FieldSample :=
  coordChange (rescale (X ω) Q (q (Fin.last 2))) (fwdMapInv W (Fin.init q 0)) Q

theorem radius_le_one' (m : ℕ) : radius m ≤ 1 := by
  unfold radius; exact pow_le_one₀ (by norm_num) (by norm_num)

/-- **The scale engine run on one rational box.** -/
theorem ae_scale_run_box [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) (γ : ℝ)
    {W : ℝ → ℝ} (hWg : DrvGood W) {d : ℂ} (hd : d ∈ Hbar) {r : ℝ} (hr : 0 < r)
    {lo hi : Fin 3 → ℚ} (hsub : ratBox lo hi ⊆ ScaleGood W d r) :
    ∀ᵐ ω ∂P, ∀ q ∈ ratBox lo hi,
      (∃ L : ℝ, Tendsto (fun ρ => ∫ v, evalReg (xS X W (Qc γ) q ω) (foldedCircle v ρ)
        ∂nuA0 W d r (Fin.init q)) (𝓝[>] 0) (𝓝 L)) ∧
      Tendsto (fun j : ℕ => ∫ v, avgReg (xS X W (Qc γ) q ω) j v ∂nuA0 W d r (Fin.init q))
        atTop (𝓝 (xS X W (Qc γ) q ω (nuA0 W d r (Fin.init q)))) := by
  rcases (ratBox lo hi).eq_empty_or_nonempty with he | hne
  · exact ae_of_all _ fun ω q hq => by rw [he] at hq; exact absurd hq (notMem_empty q)
  have hW := hWg.1
  have hW0 := hWg.2.1
  set Q := Qc γ with hQ
  obtain ⟨m₀, K, c, hF⟩ := genFam_scaleBox hWg hd hr hsub hne
  obtain ⟨q₀, hq₀⟩ := hne
  have hab : ∀ i, (lo i : ℝ) ≤ hi i := fun i =>
    (hq₀ i (mem_univ i)).1.trans (hq₀ i (mem_univ i)).2
  have hinitS : ∀ q ∈ ratBox lo hi, Fin.init q ∈ ratBox (Fin.init lo) (Fin.init hi) :=
    fun q hq i _ => hq i.castSucc (mem_univ _)
  have hlast : ∀ q ∈ ratBox lo hi, q (Fin.last 2) ∈ Icc (lo (Fin.last 2) : ℝ) (hi (Fin.last 2)) :=
    fun q hq => hq _ (mem_univ _)
  have hsnoc : ∀ p ∈ ratBox (Fin.init lo) (Fin.init hi), ∀ t : ℝ,
      t ∈ Icc (lo (Fin.last 2) : ℝ) (hi (Fin.last 2)) →
        (Fin.snoc p t : Fin 3 → ℝ) ∈ ratBox lo hi := by
    intro p hp t ht
    rw [ratBox_eq_dilSet]
    refine ⟨?_, ?_⟩
    · show Fin.init (Fin.snoc p t : Fin 3 → ℝ) ∈ _
      rw [Fin.init_snoc]; exact hp
    · show (Fin.snoc p t : Fin 3 → ℝ) (Fin.last 2) ∈ _
      rw [Fin.snoc_last]; exact ht
  have hSsub : ratBox (Fin.init lo) (Fin.init hi) ⊆ {p | ParGood W (foldSph d r) p} := by
    intro p hp
    have := (hsub (hsnoc p hp _ ⟨le_rfl, hab _⟩)).1
    rw [Fin.init_snoc] at this
    exact this
  have hs₀ : (0 : ℝ) < lo (Fin.last 2) := by
    have := (hsub (hsnoc _ (hinitS q₀ hq₀) _ ⟨le_rfl, hab _⟩)).2
    rw [Fin.snoc_last] at this
    exact this
  obtain ⟨T, a₀, a₁, δ, hT, ha₀, hδ, -, hSb, hgood, hsep⟩ :=
    boxData_A0 hr hSsub ⟨Fin.init q₀, hinitS q₀ hq₀⟩
  set S := ratBox lo hi with hSdef
  set S' := ratBox (Fin.init lo) (Fin.init hi) with hS'def
  have hSb2 : ∀ p ∈ S', p 0 ∈ Icc (0 : ℝ) T ∧ p 1 ∈ Icc a₀ a₁ := fun p hp =>
    ⟨(hSb p hp).1, (hSb p hp).2.1⟩
  have hSb3 : ∀ q ∈ S, Fin.init q 0 ∈ Icc (0 : ℝ) T ∧ Fin.init q 1 ∈ Icc a₀ a₁ ∧
      q (Fin.last 2) ∈ Icc (lo (Fin.last 2) : ℝ) (hi (Fin.last 2)) := fun q hq =>
    ⟨(hSb _ (hinitS q hq)).1, (hSb _ (hinitS q hq)).2.1, hlast q hq⟩
  have hspos : ∀ q ∈ S, 0 < q (Fin.last 2) := fun q hq => hs₀.trans_le (hlast q hq).1
  obtain ⟨n, hn⟩ := exists_nat_gt T
  have hTT : T ≤ (n : ℝ) + 1 := by linarith
  obtain ⟨Y, hYc, hYe, hreg⟩ := exists_witS hX hWg Q n
  obtain ⟨R₁, hR₁, hν⟩ := nuA0_facts hW hW0 hT.le hr ha₀ hSb2 hgood
  obtain ⟨D, hDc, hDS, hSD⟩ := TopologicalSpace.exists_countable_dense_subset S
  set R : Set ℝ := {ρ | ρ ∈ Ioc (0 : ℝ) 1 ∧ ∃ q : ℚ, (q : ℝ) = ρ} with hR
  have hRc : R.Countable := (countable_range fun q : ℚ => (q : ℝ)).mono fun ρ h => by
    obtain ⟨-, q, rfl⟩ := h; exact ⟨q, rfl⟩
  have hRI : R ⊆ Icc 0 1 := fun ρ h => ⟨h.1.1.le, h.1.2⟩
  have hRd : ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 → ∃ ρ ∈ R, a < ρ ∧ ρ < b := by
    intro a b ha hab' hb
    obtain ⟨q, h1, h2⟩ := exists_rat_btwn hab'
    exact ⟨q, ⟨⟨ha.trans_lt h1, h2.le.trans hb⟩, q, rfl⟩, h1, h2⟩
  have hinitc : Continuous fun q : Fin 3 → ℝ => Fin.init q :=
    continuous_pi fun i => continuous_apply _
  -- the inputs of the engine
  have hdetc : ContinuousOn (fun q : Fin 3 → ℝ => detLimA0 W 0 (fun _ => 0) Q d r (Fin.init q) +
      Q * Real.log (q (Fin.last 2))) S :=
    ((continuousOn_detLimA0 hW hW0 hT.le hr ha₀ hSb2 hgood 0
      (continuous_const (y := (0 : ℝ))) Q).comp hinitc.continuousOn hinitS).add
      (continuousOn_const.mul (Real.continuousOn_log.comp (continuous_apply _).continuousOn
        fun q hq => (hspos q hq).ne'))
  have hid : ∀ ρ ∈ R, ∀ q ∈ D, ∀ᵐ ω ∂P,
      ∫ v, evalReg (xS X W Q q ω) (foldedCircle v (radius m₀ * ρ)) ∂nuA0 W d r (Fin.init q) =
        X ω (dilFam (fun p ρ => muA0 W d r p (radius m₀ * ρ)) q ρ) +
          (∫ v, Dfun (vRev W (Fin.init q 0)) (Fin.init q 0) 0 (fun _ => 0) Q
            (v, radius m₀ * ρ) ∂nuA0 W d r (Fin.init q) + Q * Real.log (q (Fin.last 2))) := by
    intro ρ hρ q hq
    have hqS := hDS hq
    have hp := hinitS q hqS
    obtain ⟨hprob, hsupp, -⟩ := hν _ hp
    have hρ' : 0 < radius m₀ * ρ := mul_pos (radius_pos _) hρ.1.1
    have ht : Fin.init q 0 ∈ Icc (0 : ℝ) ((n : ℝ) + 1) :=
      ⟨(hSb _ hp).1.1, (hSb _ hp).1.2.trans hTT⟩
    filter_upwards [ae_ident_scale hX hW hW0 Q hYc hYe hreg ht (hspos q hqS) hR₁ hsupp hρ']
      with ω h
    have e : dilFam (fun p ρ => muA0 W d r p (radius m₀ * ρ)) q ρ =
        ((bindFc (nuA0 W d r (Fin.init q)) (radius m₀ * ρ)).map
          (fwdMapInv W (Fin.init q 0))).map fun z => ((q (Fin.last 2) : ℝ) : ℂ) * z := rfl
    rw [e, ← add_assoc]
    exact h
  have hdet : ∀ ε > 0, ∃ δ > 0, ∀ ρ ∈ R, ρ < δ → ∀ q ∈ S,
      |(∫ v, Dfun (vRev W (Fin.init q 0)) (Fin.init q 0) 0 (fun _ => 0) Q
          (v, radius m₀ * ρ) ∂nuA0 W d r (Fin.init q) + Q * Real.log (q (Fin.last 2))) -
        (detLimA0 W 0 (fun _ => 0) Q d r (Fin.init q) + Q * Real.log (q (Fin.last 2)))| < ε := by
    intro ε hε
    obtain ⟨ρ₀, hρ₀, h⟩ := det_unif_A0_rho hW hW0 hT.le hr ha₀ hSb2 hgood 0
      (continuous_const (y := (0 : ℝ))) Q ε hε
    refine ⟨ρ₀, hρ₀, fun ρ hρ hρρ q hq => ?_⟩
    rw [add_sub_add_right_eq_sub]
    refine h (radius m₀ * ρ) (mul_pos (radius_pos _) hρ.1.1) ?_ (Fin.init q) (hinitS q hq)
    calc radius m₀ * ρ ≤ 1 * ρ := mul_le_mul_of_nonneg_right (radius_le_one' m₀) hρ.1.1.le
      _ ≤ ρ₀ := by linarith
  have hΦc : ∀ᵐ ω ∂P, ContinuousOn (fun z : (Fin 3 → ℝ) × ℝ =>
      ∫ v, evalReg (xS X W Q z.1 ω) (foldedCircle v (radius m₀ * z.2)) ∂nuA0 W d r (Fin.init z.1))
      (S ×ˢ Ioc 0 1) := by
    filter_upwards [hreg] with ω hω
    exact continuousOn_Phi_scale hW hW0 hT hTT hr ha₀ hs₀ hSb3 hgood
      (continuousOn_witS hW hW0 (by positivity) Q ω (hYc ω))
      (fun q hq => hω _ (hspos q hq) _ ⟨(hSb3 q hq).1.1, (hSb3 q hq).1.2.trans hTT⟩) m₀
  obtain ⟨Lim, hLc, hLe, hconv⟩ := ae_unifConv_all_radii hX hF (isLipRetr_ratBox hab)
    (isCompact_ratBox lo hi) hDc hDS hSD hRc hRI hRd
    (fun ρ q ω => ∫ v, evalReg (xS X W Q q ω) (foldedCircle v (radius m₀ * ρ))
      ∂nuA0 W d r (Fin.init q))
    (fun ρ q => ∫ v, Dfun (vRev W (Fin.init q 0)) (Fin.init q 0) 0 (fun _ => 0) Q
      (v, radius m₀ * ρ) ∂nuA0 W d r (Fin.init q) + Q * Real.log (q (Fin.last 2)))
    (fun q => detLimA0 W 0 (fun _ => 0) Q d r (Fin.init q) + Q * Real.log (q (Fin.last 2)))
    hdetc hid hdet hΦc
  -- identification of the limit with the raw value
  have hrawD : ∀ᵐ ω ∂P, ∀ q ∈ D, xS X W Q q ω (nuA0 W d r (Fin.init q)) = Lim q ω := by
    refine (eventually_countable_ball hDc).2 fun q hq => ?_
    have hqS := hDS hq
    filter_upwards [ae_raw_scale hX γ hW hW0 hT hd hr ha₀ hSb hδ hgood hsep (hinitS q hqS)
      (hspos q hqS), hLe q hqS] with ω h1 h2
    have e : dilFam (fun p ρ => muA0 W d r p (radius m₀ * ρ)) q 0 =
        (muA0 W d r (Fin.init q) 0).map fun z => ((q (Fin.last 2) : ℝ) : ℂ) * z := by
      simp only [dilFam, mul_zero]
    rw [e] at h2
    exact h1.trans h2.symm
  have hrawc : ∀ᵐ ω ∂P, ContinuousOn (fun q => xS X W Q q ω (nuA0 W d r (Fin.init q))) S := by
    filter_upwards [RegSample.ae_isRegularSample hX] with ω hω
    obtain ⟨F, hF⟩ := hω
    exact continuousOn_raw_scale γ hW hW0 hT hd hr ha₀ hSb hδ hgood hsep
      (fun q hq => ⟨hinitS q hq, hspos q hq⟩) hF
  have hrad : Tendsto radius atTop (𝓝 0) := by
    unfold radius
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  filter_upwards [hconv, hreg, hrawD, hrawc] with ω hω hZ hD hc q hq
  have hqZ : IsRegularWith (xS X W Q q ω) (witS Y W Q ω (q (Fin.last 2), Fin.init q 0)) :=
    hZ _ (hspos q hq) _ ⟨(hSb3 q hq).1.1, (hSb3 q hq).1.2.trans hTT⟩
  have hνH : ∀ᵐ v ∂nuA0 W d r (Fin.init q), v ∈ Hbar :=
    (hν _ (hinitS q hq)).2.2.mono fun v hv => (show (0 : ℝ) < v.im from hv).le
  have hunif : ∀ ε > 0, ∃ δ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < δ →
      |∫ v, evalReg (xS X W Q q ω) (foldedCircle v (radius m₀ * ρ)) ∂nuA0 W d r (Fin.init q) -
        Lim q ω| ≤ ε := fun ε hε => by
    obtain ⟨δ, hδ, h⟩ := hω ε hε
    exact ⟨δ, hδ, fun ρ h0 h1 => h ρ h0 h1 q hq⟩
  refine ⟨⟨Lim q ω, Metric.tendsto_nhdsWithin_nhds.2 fun ε hε => ?_⟩, ?_⟩
  · obtain ⟨δ', hδ', h⟩ := hunif (ε / 2) (by positivity)
    refine ⟨radius m₀ * δ', mul_pos (radius_pos _) hδ', fun {ρ} hρ hρδ => ?_⟩
    have hρ0 : 0 < ρ := hρ
    rw [Real.dist_eq, sub_zero, abs_of_pos hρ0] at hρδ
    have hlt : ρ / radius m₀ < δ' := by
      rw [div_lt_iff₀ (radius_pos _)]; linarith [mul_comm δ' (radius m₀)]
    have h1 := h (ρ / radius m₀) (div_pos hρ0 (radius_pos _)) hlt
    have e : radius m₀ * (ρ / radius m₀) = ρ := by
      have := (radius_pos m₀).ne'
      field_simp
    rw [e] at h1
    rw [Real.dist_eq]
    linarith
  · have hraweq : xS X W Q q ω (nuA0 W d r (Fin.init q)) = Lim q ω := by
      have hcont : ContinuousOn
          (fun q => |xS X W Q q ω (nuA0 W d r (Fin.init q)) - Lim q ω|) S :=
        (hc.sub (hLc ω)).abs
      have h0 := le_of_continuousOn_of_dense hDS hSD hcont (ε := 0) fun q' hq' => by
        simp [hD q' hq']
      have h2 : |xS X W Q q ω (nuA0 W d r (Fin.init q)) - Lim q ω| = 0 :=
        le_antisymm (h0 q hq) (abs_nonneg _)
      rw [abs_eq_zero, sub_eq_zero] at h2
      exact h2
    rw [hraweq]
    have heqj : ∀ j : ℕ, ∫ v, avgReg (xS X W Q q ω) (j + m₀) v ∂nuA0 W d r (Fin.init q) =
        ∫ v, evalReg (xS X W Q q ω) (foldedCircle v (radius m₀ * radius j))
          ∂nuA0 W d r (Fin.init q) := fun j =>
      integral_congr_ae (hνH.mono fun v hv => by
        have hrj : radius (j + m₀) = radius m₀ * radius j := by
          unfold radius; rw [pow_add, mul_comm]
        rw [hqZ.avgReg_eq _ hv]
        show _ = evalReg (xS X W Q q ω) (foldedCircle v (radius m₀ * radius j))
        rw [hqZ.evalReg_fc_of_mem hv (mul_pos (radius_pos _) (radius_pos _)), hrj])
    have hshift : Tendsto (fun j : ℕ => ∫ v, avgReg (xS X W Q q ω) (j + m₀) v
        ∂nuA0 W d r (Fin.init q)) atTop (𝓝 (Lim q ω)) := by
      refine Metric.tendsto_atTop.2 fun ε hε => ?_
      obtain ⟨δ', hδ', h⟩ := hunif (ε / 2) (by positivity)
      obtain ⟨N, hN⟩ := eventually_atTop.1 (hrad.eventually (gt_mem_nhds hδ'))
      refine ⟨N, fun j hj => ?_⟩
      rw [Real.dist_eq, heqj j]
      exact lt_of_le_of_lt (h _ (radius_pos j) (hN j hj)) (by linarith)
    exact (tendsto_add_atTop_iff_nat m₀).1 hshift

end ASep
end QuantumZipper
