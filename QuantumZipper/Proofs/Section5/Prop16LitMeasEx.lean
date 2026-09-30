import QuantumZipper.Proofs.Section5.Prop16LitMain
import QuantumZipper.Proofs.Section5.Prop16LitMeas
import QuantumZipper.Proofs.Loewner.TwoPoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, literal form: `Prop16LitMeasStmt` from a.e. existence of the local limits

`Prop16Lit.prop16LitMeasStmt_of_exists`: the literal canonical pairings
`canPair γ (zoomFieldLit γ C (ofFun h0 + X p.1) p.2 (ψ p.2)) (B(0, r₀ p.2) ∩ ℍ) f` are
a.e.-measurable under the weighted law `prop16Q`, provided that a.s. the two local area measures
involved (of the field read through the chart on `B(0, r₀) ∩ ℍ`, and of its canonical
description on its domain) exist as vague limits (`Prop16LitExStmt`).

The proof copies the straight case `Prop16Area.Meas.aemeasurable_integral_prop16Y`
(`Prop16MeasInst.lean`): the raw coordinates of the literal field are a.e. equal to a jointly
measurable model (the translate is read through its own coordinates, the chart derivative through
the difference quotients `chartDeriv`, `Prop16LitMeas.lean`), the random half-ball
`B(0, r₀) ∩ ℍ` is the preimage of `B(0,1) ∩ ℍ` under `z ↦ z / r₀`, and the cut-offs
`isBumpFamily_comp` then give the scale parameter and the pairings. Measurability bookkeeping
only: own elementary argument (AGENT_GUIDE cost rule), following the files cited.
-/

noncomputable section

open Filter Set Metric MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Lit

open LitChart Prop16Asm Prop16Area.G

/-- **A.e. existence of the two local vague limits of the literal canonical description.** -/
def Prop16LitExStmt : Prop :=
  ∀ (γ : ℝ) (D : Set ℂ) (c d a b : ℝ) (h0 : ℂ → ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → FieldSample), Prop16Data γ D c d a b h0 P X →
    ∀ (ψ : ℝ → ℂ → ℂ) (r₀ : ℝ → ℝ), LitFamily D a b ψ r₀ → ∀ C : ℝ,
    ∀ᵐ p ∂(prop16Q γ h0 a b P X),
      (∃ m, IsVagueLimitOn (ball 0 (r₀ p.2) ∩ H)
        (areaApprox γ (zoomFieldLit γ C (ofFun h0 + X p.1) p.2 (ψ p.2))) m) ∧
      (∃ m, IsVagueLimitOn (canonicalDomainOn γ (zoomFieldLit γ C (ofFun h0 + X p.1) p.2 (ψ p.2))
          (ball 0 (r₀ p.2) ∩ H))
        (areaApprox γ (canonicalOn γ (zoomFieldLit γ C (ofFun h0 + X p.1) p.2 (ψ p.2))
          (ball 0 (r₀ p.2) ∩ H))) m)

namespace MeasEx

open Prop16Area Prop16Area.Meas Factorization

variable {α : Type*} [MeasurableSpace α]

/-- `evalReg` along a measurable family of push-forwards is measurable. -/
theorem measurable_evalReg_map {Y : α → FieldSample} (hY : Measurable Y) {g : α → ℂ → ℂ}
    (hg : Measurable fun q : α × ℂ => g q.1 q.2) (m : Measure ℂ) [SFinite m] :
    Measurable fun p => evalReg (Y p) (m.map (g p)) := by
  have hF : ∀ k : ℕ, Measurable fun q : α × ℂ => avgReg (Y q.1) k (g q.1 q.2) := fun k =>
    (measurable_avgReg k).comp ((hY.comp measurable_fst).prodMk hg)
  have hint : ∀ k : ℕ, ∀ p : α,
      ∫ w, avgReg (Y p) k w ∂(m.map (g p)) = ∫ u, avgReg (Y p) k (g p u) ∂m := by
    intro k p
    have hs : Measurable fun w : ℂ => avgReg (Y p) k w :=
      (measurable_avgReg k).comp (measurable_const.prodMk measurable_id)
    exact integral_map (hg.comp (measurable_const.prodMk measurable_id)).aemeasurable
      hs.aestronglyMeasurable
  unfold evalReg
  simp_rw [hint]
  have hk : ∀ k : ℕ, StronglyMeasurable fun p : α => ∫ u, avgReg (Y p) k (g p u) ∂m := fun k =>
    StronglyMeasurable.integral_prod_right' (hF k).stronglyMeasurable
  exact (StronglyMeasurable.limUnder hk).measurable

/-- `B(0, r) ∩ ℍ` is the preimage of `B(0, 1) ∩ ℍ` under `z ↦ r⁻¹ z`. -/
theorem preimage_inv_mul_hb {r : ℝ} (hr : 0 < r) :
    (fun z : ℂ => ((r : ℂ))⁻¹ * z) ⁻¹' (ball (0 : ℂ) 1 ∩ H) = ball (0 : ℂ) r ∩ H := by
  have e : ((r : ℂ))⁻¹ = ((r⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  ext z
  simp only [mem_preimage, mem_inter_iff, mem_ball, dist_zero_right, H, mem_ofPred_eq, e,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hr, Complex.im_ofReal_mul]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rwa [inv_mul_lt_one₀ hr] at h1
    · exact (pos_iff_pos_of_mul_pos h2).1 (inv_pos.2 hr)
  · rintro ⟨h1, h2⟩
    exact ⟨(inv_mul_lt_one₀ hr).2 h1, mul_pos (inv_pos.2 hr) h2⟩

/-- **Canonical pairings on random half-balls, generic form.** If the raw coordinates of `Z p`
are a.e. equal to a measurable family, the radius is measurable and a.e. positive, and the two
local vague limits exist a.e., then the canonical pairings on `B(0, r p) ∩ ℍ` are
a.e.-measurable (the proof of `Prop16Area.Meas.aemeasurable_integral_prop16Y`). -/
theorem aemeasurable_canPair_ball {γ : ℝ} {μ : Measure α} {Z : α → FieldSample} {r : α → ℝ}
    (hr : Measurable r) (hr0 : ∀ᵐ p ∂μ, 0 < r p)
    {y : α → ℕ → ℝ} (hy : Measurable y) (hyZ : ∀ᵐ p ∂μ, coords (Z p) = y p)
    (hG0 : ∀ᵐ p ∂μ, ∃ m, IsVagueLimitOn (ball 0 (r p) ∩ H) (areaApprox γ (Z p)) m)
    (hG1 : ∀ᵐ p ∂μ, ∃ m, IsVagueLimitOn (canonicalDomainOn γ (Z p) (ball 0 (r p) ∩ H))
        (areaApprox γ (canonicalOn γ (Z p) (ball 0 (r p) ∩ H))) m)
    {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    AEMeasurable (fun p => canPair γ (Z p) (ball 0 (r p) ∩ H) f) μ := by
  have hbo : IsOpen (ball (0 : ℂ) 1 ∩ H) := isOpen_ball.inter isOpen_H
  have hbc : (ball (0 : ℂ) 1 ∩ H)ᶜ.Nonempty := ⟨0, fun h => by simpa [H] using h.2⟩
  have hrC : Measurable fun p => ((r p : ℂ))⁻¹ := (Complex.measurable_ofReal.comp hr).inv
  set Z' : α → FieldSample := fun p => reconstruct (y p) with hZ'def
  have hZ' : Measurable Z' := measurable_reconstruct.comp hy
  set V : α → Set ℂ := fun p => (fun z : ℂ => ((r p : ℂ))⁻¹ * z) ⁻¹' (ball 0 1 ∩ H) with hVdef
  have hφ := isBumpFamily_comp (α := α) hbo hbc (g := fun p z => ((r p : ℂ))⁻¹ * z)
    ((hrC.comp measurable_fst).mul measurable_snd) (fun p => by fun_prop)
  have hrec : ∀ᵐ p ∂μ, Z' p = recon (Z p) := hyZ.mono fun p hp => by
    simp only [hZ'def, recon, hp]
  have hV : ∀ᵐ p ∂μ, V p = ball 0 (r p) ∩ H := hr0.mono fun p hp => preimage_inv_mul_hb hp
  have hs : ∀ᵐ p ∂μ, scaleParamOn γ (Z' p) (V p) = scaleParamOn γ (Z p) (ball 0 (r p) ∩ H) := by
    filter_upwards [hrec, hV] with p h1 h2
    rw [h1, h2, scaleParamOn_recon]
  have hG0' : NullMeasurableSet (goodSet γ Z' V) μ := nullMeasurableSet_of_ae (by
    filter_upwards [hrec, hV, hG0] with p h1 h2 h3
    show ∃ m, IsVagueLimitOn (V p) (areaApprox γ (Z' p)) m
    rw [h1, h2, areaApprox_recon]
    exact h3)
  have ha := (aemeasurable_scaleParamOn (γ := γ) hZ' hφ hG0').congr hs
  have hyc : AEMeasurable (fun p => coords (Z p)) μ :=
    hy.aemeasurable.congr (hyZ.mono fun p hp => hp.symm)
  have hy2 := aemeasurable_coords_canonicalOn γ Z (fun p => ball 0 (r p) ∩ H) hyc ha
  obtain ⟨a', ham, ha_ae⟩ := ha
  obtain ⟨y', hym, hy_ae⟩ := hy2
  set W : α → Set ℂ := fun p =>
    (fun z : ℂ => ((r p : ℂ))⁻¹ * ((a' p : ℂ) * z)) ⁻¹' (ball 0 1 ∩ H) with hWdef
  have hφ' := isBumpFamily_comp (α := α) hbo hbc
    (g := fun p z => ((r p : ℂ))⁻¹ * ((a' p : ℂ) * z))
    ((hrC.comp measurable_fst).mul
      ((Complex.measurable_ofReal.comp (ham.comp measurable_fst)).mul measurable_snd))
    (fun p => by fun_prop)
  have hx : Measurable fun p => reconstruct (y' p) := measurable_reconstruct.comp hym
  have hae : ∀ᵐ p ∂μ,
      qAreaMeasureOn γ (canonicalOn γ (Z p) (ball 0 (r p) ∩ H))
          (canonicalDomainOn γ (Z p) (ball 0 (r p) ∩ H)) =
        qAreaMeasureOn γ (reconstruct (y' p)) (W p) ∧
      ((∃ m, IsVagueLimitOn (canonicalDomainOn γ (Z p) (ball 0 (r p) ∩ H))
          (areaApprox γ (canonicalOn γ (Z p) (ball 0 (r p) ∩ H))) m) =
        (∃ m, IsVagueLimitOn (W p) (areaApprox γ (reconstruct (y' p))) m)) := by
    filter_upwards [ha_ae, hy_ae, hr0] with p h1 h2 h3
    have hU : canonicalDomainOn γ (Z p) (ball 0 (r p) ∩ H) = W p := by
      ext z
      simp only [hWdef, canonicalDomainOn, mem_preimage]
      rw [h1, ← preimage_inv_mul_hb h3]
      exact Iff.rfl
    have hA : areaApprox γ (reconstruct (y' p)) =
        areaApprox γ (canonicalOn γ (Z p) (ball 0 (r p) ∩ H)) := by
      rw [← h2]; exact areaApprox_recon γ _
    refine ⟨?_, ?_⟩
    · rw [hU, ← h2]; exact (qAreaMeasureOn_recon γ _ _).symm
    · rw [hU, hA]
  have hG1' : NullMeasurableSet (goodSet γ (fun p => reconstruct (y' p)) W) μ :=
    nullMeasurableSet_of_ae (by
      filter_upwards [hae, hG1] with p hp h
      show ∃ m, IsVagueLimitOn (W p) (areaApprox γ (reconstruct (y' p))) m
      rw [← hp.2]
      exact h)
  refine (aemeasurable_integral_qAreaMeasureOn (μ := μ) hx hφ' hG1' hf hfc).congr ?_
  filter_upwards [hae] with p hp
  show _ = ∫ z, f z ∂qAreaMeasureOn γ (canonicalOn γ (Z p) (ball 0 (r p) ∩ H))
    (canonicalDomainOn γ (Z p) (ball 0 (r p) ∩ H))
  rw [hp.1]

end MeasEx

/-- The folded circle of index `i` (the measure read by the `i`-th raw coordinate). -/
abbrev fcI (i : ℕ) : Measure ℂ := foldedCircle (Factorization.dyadicIndex i).1
  (radius (Factorization.dyadicIndex i).2)

/-- **`Prop16LitMeasStmt` from a.e. existence of the two local vague limits.** -/
theorem prop16LitMeasStmt_of_exists (hEx : Prop16LitExStmt) : Prop16LitMeasStmt := by
  intro γ D c d a b h0 Ω _ P X hdat ψ r₀ hfam C f hf hfs
  obtain ⟨hψm, hr₀m, hch⟩ := hfam
  obtain ⟨-, -, -, -, -, -, -, -, hmix, -, hfin⟩ := id hdat
  have hXm : ∀ μ : Measure ℂ, Measurable fun ω => X ω μ := hmix.measurable_coord
  have hloc := prop16LocGoodStmt_of_coupling prop16MixedFreeLocCoupling_mm
  have hν := prop16NuMeasStmt_of_loc hloc γ D c d a b h0 P X hdat
  have hta : ∀ᵐ p ∂(prop16Q γ h0 a b P X), p.2 ∈ Ioo a b :=
    ae_prop16Law_of_ae (G := fun _ t => t ∈ Ioo a b) (aemeasurable_prop16Kernel' hν hfin)
      (fun ω => sFinite_prop16Nu γ h0 a b (X ω)) (fun ω => prop16Nu_compl_Ioo γ h0 a b (X ω))
      (ae_of_all _ fun _ _ ht => ht)
  -- the measurable model of the raw coordinates
  obtain ⟨T, hTdef⟩ : ∃ T : Ω × ℝ → FieldSample, T = fun p =>
      Factorization.reconstruct (Factorization.coords (translate (ofFun h0 + X p.1) (p.2 : ℂ))) :=
    ⟨_, rfl⟩
  have hT : Measurable T := by
    rw [hTdef]
    refine Factorization.measurable_reconstruct.comp ?_
    exact Measurable.comp (g := fun q : FieldSample × ℝ =>
        Factorization.coords (translate q.1 (q.2 : ℂ)))
      (f := fun p : Ω × ℝ => (ofFun h0 + X p.1, p.2))
      IndepParams.measurable_coords_translate
      (((Prop16Area.measurable_ofFun_add h0 hXm).comp measurable_fst).prodMk measurable_snd)
  obtain ⟨y, hydef⟩ : ∃ y : Ω × ℝ → ℕ → ℝ, y = fun p i =>
      (evalReg (T p) ((fcI i).map (ψ p.2)) +
        Qc γ * ∫ u, Real.log ‖chartDeriv ψ (p.2, u)‖ ∂(fcI i)) + C / γ * ((fcI i) univ).toReal :=
    ⟨_, rfl⟩
  have hy : Measurable y := by
    rw [hydef]
    refine measurable_pi_iff.2 fun i => ?_
    have hlog : Measurable fun q : (Ω × ℝ) × ℂ => Real.log ‖chartDeriv ψ (q.1.2, q.2)‖ :=
      Real.measurable_log.comp ((measurable_chartDeriv hψm).comp
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd)).norm
    refine ((MeasEx.measurable_evalReg_map hT (g := fun p z => ψ p.2 z)
      (hψm.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)) _).add
      (measurable_const.mul ?_)).add measurable_const
    exact (StronglyMeasurable.integral_prod_right' hlog.stronglyMeasurable).measurable
  have hyZ : ∀ᵐ p ∂(prop16Q γ h0 a b P X),
      Factorization.coords (zoomFieldLit γ C (ofFun h0 + X p.1) p.2 (ψ p.2)) = y p := by
    filter_upwards [hta] with p hp
    funext i
    have hd : ∀ᵐ u ∂(fcI i), DifferentiableAt ℂ (ψ p.2) u :=
      (TwoPoint.foldedCircle_ae_mem_H _ (radius_pos _)).mono fun u hu =>
        ((hch p.2 hp).1 u hu).differentiableAt (isOpen_H.mem_nhds hu)
    have hi : ∫ u, Real.log ‖deriv (ψ p.2) u‖ ∂(fcI i) =
        ∫ u, Real.log ‖chartDeriv ψ (p.2, u)‖ ∂(fcI i) :=
      integral_congr_ae (hd.mono fun u hu => by simp only [chartDeriv_eq hu])
    show zoomFieldLit γ C (ofFun h0 + X p.1) p.2 (ψ p.2) (fcI i) = y p i
    rw [hydef, hTdef]
    simp only [zoomFieldLit, addConst, coordChange, hi]
    rw [Factorization.evalReg_congr (Factorization.avgReg_reconstruct_coords _)]
  have hr0 : ∀ᵐ p ∂(prop16Q γ h0 a b P X), 0 < r₀ p.2 :=
    hta.mono fun p hp => (hch p.2 hp).2.2.2.1
  have hE := hEx γ D c d a b h0 P X hdat ψ r₀ ⟨hψm, hr₀m, hch⟩ C
  refine MeasEx.aemeasurable_canPair_ball (γ := γ) (μ := prop16Q γ h0 a b P X)
    (Z := fun p => zoomFieldLit γ C (ofFun h0 + X p.1) p.2 (ψ p.2))
    (r := fun p => r₀ p.2) ?_ hr0 hy hyZ ?_ ?_ hf hfs
  · exact hr₀m.comp measurable_snd
  · exact hE.mono fun _ h => h.1
  · exact hE.mono fun _ h => h.2

end Prop16Lit

end QuantumZipper
