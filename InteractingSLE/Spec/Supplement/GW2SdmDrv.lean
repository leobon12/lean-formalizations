/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdlNorm
import InteractingSLE.Spec.Sec6.DrivingCriterion
import InteractingSLE.Spec.Sec7.Lemma71Capacity

/-!
# GW2's stage mean, clause (G2): the Brownian scaling of the drivers from the chart dilation

Packet PROVE-GW2-STAGEMEAN, driver-scaling round. `GW2Sdl.StageDilationAt` asks, besides the chart dilation
`ca.1 = λ · cs.1` (derived last round from two tip normalizations, `GW2Sdl.eq_dilationFactor`), that the stage driver be
the Brownian rescaling of the kernel-route driver. This file DERIVES that clause from the chart dilation and the
domain identities of the two charts at every stage time (each chart maps the complement of the stage union onto the
complement of its own Loewner hull):

* **`mem_fwdHull_iff_of_chart_dilation`**: if `ca.1 = λ · cs.1` on the stage-start domain and
  `cs⁻¹(ℍ ∖ K^S_u) = ca⁻¹(ℍ ∖ K^{Sn}_{u'})`, then `z ∈ K^S_u ↔ λ z ∈ K^{Sn}_{u'}` for `z ∈ ℍ`;
* **`time_eq_of_mem_iff`**: then `u' = λ² u` (half-plane capacity, `hcap K_s = 2s`, `hcap(λK) = λ² hcap K`);
* **`driver_eqOn_scale`**: hull scaling on `[0, Q]` gives `S = Sn(λ² ·)/λ` on `[0, Q]` (Loewner uniqueness,
  `Sec6.eqOn_of_fwdHull_eq`);
* **`driver_scale_of_domains`**: the combination;
* **`read_of_dilation_eqOn`**, **`StageDilationOnAt`** (named input: the dilation data with the driver clause only on
  `[0, clock]`, which is what the hulls determine) and **`stagePhysLawAt_of_dilationOn`**.

Deterministic except for the packaging. Conditional helper with distinct names; it replaces no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H fwdHull fwdMap fwdMapInv logDerivFwd chiC zeroGFFTestCov)

universe u

namespace InteractingSLE.Theorem14.GW2Sdm

open GW2KM2 Restart Restart.DomainMarkov Restart.FCDet Exist.StagedLaw Sec7.PocketTraversal Supp8.GB6
  Supp8.GB6.RelDrv Supp8.Q3Stop Supp8.GB6.HullId Supp8.RelSafe GW2Rd GW2Sde GW2TipSystem GW2TipSystem.RootC24
  LocalSets WholeField Supp8.RelSafeS GW2Stl GW2Scl GW2Spm GW2Sdl

/-- A Loewner hull lies in `ℍ`. -/
theorem fwdHull_subset_H' {W : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t) : fwdHull W t ⊆ H := fun z hz =>
  ((QuantumZipper.LoewnerAlgebra.mem_fwdHull_iff ht z).1 hz).1

theorem mul_mem_H_iff {a : ℝ} (ha : 0 < a) (z : ℂ) : (a : ℂ) * z ∈ H ↔ z ∈ H := by
  show 0 < ((a : ℂ) * z).im ↔ 0 < z.im
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  exact ⟨fun h => pos_of_mul_pos_right h ha.le, fun h => mul_pos ha h⟩

/-- **Hull membership through a chart dilation.** -/
theorem mem_fwdHull_iff_of_chart_dilation {cs ca : Chart} (hcs : cs.IsConformal) (hca : ca.IsConformal) {lam : ℝ}
    (hlam : 0 < lam) (hfwd : ∀ x ∈ cs.2.1 '' H, ca.1 x = (lam : ℂ) * cs.1 x) {S Sn : ℝ → ℝ} {u u' : ℝ}
    (hD : cs.2.1 '' (H \ fwdHull S u) = ca.2.1 '' (H \ fwdHull Sn u')) :
    ∀ z ∈ H, z ∈ fwdHull S u ↔ (lam : ℂ) * z ∈ fwdHull Sn u' := by
  intro z hz
  have hlz : (lam : ℂ) * z ∈ H := (mul_mem_H_iff hlam z).2 hz
  have hlam' : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
  have key : z ∉ fwdHull S u ↔ (lam : ℂ) * z ∉ fwdHull Sn u' := by
    constructor
    · intro hzK
      have hx : cs.2.1 z ∈ ca.2.1 '' (H \ fwdHull Sn u') := by
        rw [← hD]
        exact mem_image_of_mem _ ⟨hz, hzK⟩
      obtain ⟨v, hv, hvx⟩ := hx
      have h1 : ca.1 (cs.2.1 z) = v := by rw [← hvx, hca.2.2 v hv.1]
      have h2 : ca.1 (cs.2.1 z) = (lam : ℂ) * z := by
        rw [hfwd _ (mem_image_of_mem _ hz), hcs.2.2 z hz]
      rw [← h2, h1]
      exact hv.2
    · intro hlK
      have hx : ca.2.1 ((lam : ℂ) * z) ∈ cs.2.1 '' (H \ fwdHull S u) := by
        rw [hD]
        exact mem_image_of_mem _ ⟨hlz, hlK⟩
      obtain ⟨z', hz', hzx⟩ := hx
      have h1 : ca.1 (ca.2.1 ((lam : ℂ) * z)) = (lam : ℂ) * z := hca.2.2 _ hlz
      have h2 : ca.1 (cs.2.1 z') = (lam : ℂ) * z' := by
        rw [hfwd _ (mem_image_of_mem _ hz'.1), hcs.2.2 z' hz'.1]
      rw [hzx, h1] at h2
      have hzz : z = z' := mul_left_cancel₀ hlam' h2
      rw [hzz]
      exact hz'.2
  exact not_iff_not.1 key

/-- **The time of the kernel-route hull is `λ²` times the stage time** (half-plane capacity). -/
theorem time_eq_of_mem_iff {S Sn : ℝ → ℝ} (hS : Continuous S) (hS0 : S 0 = 0) (hSn : Continuous Sn)
    (hSn0 : Sn 0 = 0) {lam : ℝ} (hlam : 0 < lam) {u u' : ℝ} (hu : 0 ≤ u) (hu' : 0 ≤ u')
    (h : ∀ z ∈ H, z ∈ fwdHull S u ↔ (lam : ℂ) * z ∈ fwdHull Sn u') : u' = lam ^ 2 * u := by
  have hlam' : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
  have hl2 : (lam ^ 2 : ℝ) ≠ 0 := by positivity
  set Sh : ℝ → ℝ := fun r => lam * S (r / lam ^ 2) with hShdef
  have hShc : Continuous Sh := continuous_const.mul (hS.comp (continuous_id.div_const _))
  have hSh0 : Sh 0 = 0 := by simp [hShdef, hS0]
  have hShS : (fun s => Sh (lam ^ 2 * s) / lam) = S := by
    funext s
    simp only [hShdef]
    rw [mul_div_cancel_left₀ _ hl2]
    field_simp
  have hhull : fwdHull Sh (lam ^ 2 * u) = fwdHull Sn u' := by
    ext w
    have hz := QuantumZipper.LoewnerAlgebra.mem_fwdHull_scale_iff Sh hlam hu (w / lam)
    rw [hShS, mul_div_cancel₀ _ hlam'] at hz
    by_cases hw : w ∈ H
    · have hwH : w / lam ∈ H := by
        rw [← mul_mem_H_iff hlam, mul_div_cancel₀ _ hlam']
        exact hw
      have h' := h (w / lam) hwH
      rw [mul_div_cancel₀ _ hlam'] at h'
      rw [← hz, h']
    · exact iff_of_false (fun h' => hw (fwdHull_subset_H' (by positivity) h'))
        (fun h' => hw (fwdHull_subset_H' hu' h'))
  have e1 := Sec7.Lemma71.hcapSet_eq_of_fwdHull_eq hShc hSh0 (by positivity) hhull
  have e2 := Sec7.Lemma71.hcapSet_eq_of_fwdHull_eq hSn hSn0 hu' (rfl : fwdHull Sn u' = fwdHull Sn u')
  rw [e1] at e2
  linarith

/-- **Hull scaling on `[0, Q]` gives the Brownian scaling of the drivers on `[0, Q]`.** -/
theorem driver_eqOn_scale {S Sn : ℝ → ℝ} (hS : Continuous S) (hS0 : S 0 = 0) (hSn : Continuous Sn)
    (hSn0 : Sn 0 = 0) {lam : ℝ} (hlam : 0 < lam) {Q : ℝ} (hQ : 0 ≤ Q)
    (h : ∀ u ∈ Icc 0 Q, ∀ z ∈ H, z ∈ fwdHull S u ↔ (lam : ℂ) * z ∈ fwdHull Sn (lam ^ 2 * u)) :
    EqOn S (fun s => Sn (lam ^ 2 * s) / lam) (Icc 0 Q) := by
  have hS'c : Continuous fun s => Sn (lam ^ 2 * s) / lam := (hSn.comp (continuous_const.mul continuous_id)).div_const _
  have hS'0 : (fun s => Sn (lam ^ 2 * s) / lam) 0 = 0 := by simp [hSn0]
  refine Sec6.eqOn_of_fwdHull_eq hS hS'c hS0 hS'0 hQ fun u hu => ?_
  ext z
  by_cases hz : z ∈ H
  · rw [h u hu z hz, QuantumZipper.LoewnerAlgebra.mem_fwdHull_scale_iff Sn hlam hu.1 z]
  · exact iff_of_false (fun h' => hz (fwdHull_subset_H' hu.1 h')) (fun h' => hz (fwdHull_subset_H' hu.1 h'))

/-- **The Brownian scaling of the drivers from the chart dilation and the domain identities.** -/
theorem driver_scale_of_domains {cs ca : Chart} (hcs : cs.IsConformal) (hca : ca.IsConformal) {lam : ℝ}
    (hlam : 0 < lam) (hfwd : ∀ x ∈ cs.2.1 '' H, ca.1 x = (lam : ℂ) * cs.1 x) {S Sn : ℝ → ℝ}
    (hS : Continuous S) (hS0 : S 0 = 0) (hSn : Continuous Sn) (hSn0 : Sn 0 = 0) {Q : ℝ} (hQ : 0 ≤ Q)
    (hD : ∀ u ∈ Icc 0 Q, ∃ u' : ℝ, 0 ≤ u' ∧ cs.2.1 '' (H \ fwdHull S u) = ca.2.1 '' (H \ fwdHull Sn u')) :
    EqOn S (fun s => Sn (lam ^ 2 * s) / lam) (Icc 0 Q) := by
  refine driver_eqOn_scale hS hS0 hSn hSn0 hlam hQ fun u hu => ?_
  obtain ⟨u', hu', hDu⟩ := hD u hu
  have hmem := mem_fwdHull_iff_of_chart_dilation hcs hca hlam hfwd hDu
  have ht := time_eq_of_mem_iff hS hS0 hSn hSn0 hlam hu.1 hu' hmem
  rw [ht] at hmem
  exact hmem

/-! ### (G2) with the driver clause on `[0, clock]` -/

/-- **The kernel-route mean read in the stage chart, per sample, with the drivers related only on `[0, q]`.** -/
theorem read_of_dilation_eqOn {κ σa kc : ℝ} {cs ca : Chart} (hcs : cs.IsConformal) {D : Set ℂ} {S Sn : ℝ → ℝ}
    {q lam : ℝ} (hlam : 0 < lam) (hq : 0 ≤ q) {U Uca u₀ : ℂ → ℝ}
    (hD : ∀ z ∈ H \ fwdHull S q, cs.2.1 z ∈ D)
    (hfwd : ∀ x ∈ D, ca.1 x = (lam : ℂ) * cs.1 x) (hlift : ∀ x ∈ D, ca.2.2 x = cs.2.2 x)
    (hS : EqOn S (fun s => Sn (lam ^ 2 * s) / lam) (Icc 0 q)) (hSc : Continuous S)
    (hU : EqOn (fun w => Uca (lam * w)) U H) :
    ∀ z ∈ H \ fwdHull S q,
      (couplingMean κ Sn (lam ^ 2 * q) Uca (ca.1 (cs.2.1 z)) - u₀ (cs.2.1 z) - σa - kc * ca.2.2 (cs.2.1 z)) +
          u₀ (cs.2.1 z) + σa + kc * cs.2.2 (cs.2.1 z) = couplingMean κ S q U z := by
  intro z hz
  have hx := hD z hz
  rw [hfwd _ hx, hlift _ hx, hcs.2.2 z hz.1]
  have hfH : fwdMap S q z ∈ H := QuantumZipper.FwdHolo.mapsTo_fwdMap hSc hq hz
  have e0 : couplingMean κ S q U z = couplingMean κ S q (fun w => Uca (lam * w)) z := by
    unfold couplingMean
    rw [hU hfH]
  have e1 : couplingMean κ S q (fun w => Uca (lam * w)) z =
      couplingMean κ (fun s => Sn (lam ^ 2 * s) / lam) q (fun w => Uca (lam * w)) z :=
    Sec5.Markov.couplingMean_congr_of_eqOn hS hq le_rfl κ _ z
  rw [e0, e1, couplingMean_scale κ Sn hlam hq Uca z]
  ring

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q}
  {l : List (EntryIdx c.Θ c.Q)}

/-- **Named input: the dilation data of a stage at time `t`, drivers related on `[0, clock]`** (the form the hulls
determine, `driver_scale_of_domains`; otherwise as `GW2Sdl.StageDilationAt`). -/
def StageDilationOnAt (I : StageInst Ω) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (w : WordType) (t : ℝ≥0) (G : Set Ω) (ca : Ω → Chart) (Sn : Ω → ℝ → ℝ)
    (lam : Ω → ℝ) (Uca : Ω → ℂ → ℝ) : Prop :=
  ∀ᵐ ω ∂c.P, ω ∈ G → 0 < lam ω ∧
    (∀ x ∈ H \ I.B t ω, (ca ω).1 x = (lam ω : ℂ) * (I.chart c ω).1 x ∧ (ca ω).2.2 x = (I.chart c ω).2.2 x) ∧
    EqOn (fun s : ℝ => I.drv c s.toNNReal ω) (fun s => Sn ω (lam ω ^ 2 * s) / lam ω)
      (Icc 0 ((I.clock c t ω).toNNReal : ℝ)) ∧
    EqOn (fun w => Uca ω (lam ω * w))
      (bheProc c.κ (typedRhoL w) (typedRhoR w) (I.drv c)
        (fun i t ω => geomLW canonDrv (fun y => typedXL c.κ w (I.β y.1)) i t
          (I.srec c r l ω, relVar I.Hr (I.drv c) (I.cap c) ω))
        (fun j t ω => geomRW canonDrv (fun y => typedXR c.κ w (I.β y.1)) j t
          (I.srec c r l ω, relVar I.Hr (I.drv c) (I.cap c) ω)) ω
        (I.clock c t ω).toNNReal) H

/-- **`StagePhysLawAt` from the kernel route, with the drivers related on `[0, clock]`.** -/
theorem stagePhysLawAt_of_dilationOn (I : StageInst Ω) (hv : IsGB6RelVersion c.s c.P I.W c.W c.ζ I.γ c.α I.R I.V)
    (hpre : Measurable (stgPreRec c.s I.W c.W c.ζ I.GT I.V I.T I.R)) (w : WordType) (t : ℝ≥0)
    {G : Set Ω} (hG : MeasurableSet[I.ℋ t] G)
    (hlive : ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w I.β I.E (I.srec c r l) → I.clock c t ω < I.cap c ω → ω ∈ G)
    {ca : Ω → Chart} {Sn : Ω → ℝ → ℝ} {lam : Ω → ℝ} {Uca : Ω → ℂ → ℝ}
    (hMh : ∀ ω, InnerProductSpace.HarmonicOnNhd (caMean I c ca Sn lam Uca t ω) (H \ I.B t ω))
    (hlaw : ∀ (φ : TestOn upperHalfPlaneOpens) (ρ : ℝ), ∀ᵐ ω ∂c.P, ω ∈ G → tsupport φ ⊆ H \ I.B t ω →
      (c.P[fun ω' => Complex.exp (Complex.I * ((ρ * centredField c.h I.u₀ ω' φ : ℝ) : ℂ)) | I.ℋ t]) ω =
        Complex.exp (Complex.I * ((ρ * ∫ z, caMean I c ca Sn lam Uca t ω z * φ z : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * (ρ ^ 2 * zeroGFFTestCov (H \ I.B t ω) φ φ)) : ℝ) : ℂ))
    (hshape : ∀ᵐ ω ∂c.P, ω ∈ G → H \ I.B t ω = (I.chart c ω).2.1 ''
      (H \ fwdHull (fun s : ℝ => I.drv c s.toNNReal ω) ((I.clock c t ω).toNNReal : ℝ)))
    (hdil : StageDilationOnAt I c r l w t G ca Sn lam Uca) :
    StagePhysLawAt I c r l w t := by
  have hmc := isMeasChart_stgChart (measurable_gb6Rec_src c) hv.2.1 hv.2.2.1 hpre
  refine ⟨G, caMean I c ca Sn lam Uca t, hG, hlive, hMh, hlaw, ?_⟩
  filter_upwards [hshape, hdil] with ω hsh hd hωG
  obtain ⟨hlam, hch, hS, hU⟩ := hd hωG
  have hSc : Continuous fun s : ℝ => I.drv c s.toNNReal ω :=
    (continuous_stgDrv (hv.2.1 ω) _).comp continuous_real_toNNReal
  intro z hz
  exact read_of_dilation_eqOn (κ := c.κ) (σa := I.σa) (kc := I.kc) (u₀ := I.u₀) (hmc.1 ω) hlam
    (NNReal.coe_nonneg _) (D := H \ I.B t ω)
    (fun z hz => by rw [hsh hωG]; exact mem_image_of_mem _ hz)
    (fun x hx => (hch x hx).1) (fun x hx => (hch x hx).2) hS hSc hU z hz

end InteractingSLE.Theorem14.GW2Sdm
