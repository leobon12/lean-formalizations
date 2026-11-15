/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.StoppedCont
import InteractingSLE.Spec.Exist.StagedCongr
import InteractingSLE.Spec.Exist.TransferHull
import QuantumZipper.Proofs.Thm11.ExtMeasCont

/-!
# WFS-0: couplings through a stop with a full evolution

Packet PROVE-WFS0, item WFS-0 of `planning/handoffs/PROVE-DOMAINMARKOV10.md` §4.2. The stopped kernel (K) needs the
whole-field machinery WF2–WF9 and Aux50Hit for a coupling known only through a stop `V`. Those proofs use a full
evolution (path facts, dyadic approximations), but the frozen clauses only at stops before `V`. This file defines the
interface they will be copied against and derives it from a stopped coupling:

* **`IsCouplingThrough κ xL xR ρL ρR P 𝓕 W VL VR B ζ V h`**: a full integrated evolution with lifetime `ζ`, a stop
  `V ≤ ζ`, a measurable field whose centred part is a zero-boundary GFF, and the frozen clauses of Theorem 1.1 (local
  hull, conditional law of the field off the hull) at every stopping time `τ` of the driving filtration of the
  coordinates **killed at `V`** with `τ < V` almost surely (as in `StoppedExtend.IsStoppedHullCoupling`, whose clauses
  are at `τ ≤ V`; at `τ = V` its hull reads the driver after `V`, which a stopped coupling does not constrain, so only
  `τ < V` transfers);
* **`isCouplingThrough_of_continuation`**: a stopped coupling, read on any continuation of its evolution (a full
  evolution on an enlargement `π : Ω' → Ω` agreeing with it before `V`), is a coupling through `V ∘ π ∧ ζ'` with the
  field `h ∘ π`. The driving filtration killed at the stop on `Ω'` is the usual augmentation of the pull-back of the one
  on `Ω` (`Exist.drivingFiltration_congr_ae`, `Exist.drivingFiltration_comp`); a stopping time of it is almost surely
  `s ∘ π` for a stopping time `s` of the stopped coupling (`Exist.exists_isStoppingTime_ae_eq_comp`, Doob–Dynkin); the
  local-set clause transfers along the law, and the conditional expectations along `π`
  (`Exist.condExp_comp_ae_eq`), the hull, the mean and the energy only seeing the driver before `V`;
* **`exists_isCouplingThrough`**: with (CONT) (`Restart.StoppedCont.stoppedContinuationStatement`), every stopped
  coupling (`κ > 0`) has such a continuation.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace WFS

open Restart StoppedExtend Exist Exist.Staged QuantumZipper LQGMetric

/-! ### Auxiliary transfers -/

section Aux

/-- **A local set read through a measure-preserving map is a local set** (the definition only involves the law of the
pair). -/
theorem isLocalSet_comp {Ω Ω' : Type u} [MeasurableSpace Ω] [MeasurableSpace Ω'] {A : Ω → Set ℂ}
    {h : Ω → DistOn upperHalfPlaneOpens} {P : Measure Ω} (hA : IsLocalSet A h P) {π : Ω' → Ω}
    (hπ : Measurable π) {P' : Measure Ω'} (hπP : P'.map π = P) :
    IsLocalSet (fun p => A (π p)) (fun p => h (π p)) P' := by
  let _ : MeasurableSpace (Set ℂ) := hittingSigma
  obtain ⟨hm, hsub, Ω₂, m₂, P₂, hP₂, A₂, h₁, h₂, hA₂, hh₁, hh₂, hA₂H, hharm, hcond, hlaw⟩ := hA
  have hm' : AEMeasurable (fun ω => (A ω, h ω)) (P'.map π) := by rw [hπP]; exact hm
  refine ⟨hm'.comp_aemeasurable hπ.aemeasurable, ?_, Ω₂, m₂, P₂, hP₂, A₂, h₁, h₂, hA₂, hh₁, hh₂, hA₂H, hharm,
    hcond, ?_⟩
  · rw [← hπP] at hsub
    exact ae_of_ae_map hπ.aemeasurable hsub
  · rw [hlaw, ← hπP, AEMeasurable.map_map_of_aemeasurable hm' hπ.aemeasurable]
    rfl

/-- **Off the hull the centred Loewner map stays in `ℍ`**, for a driver continuous on `[0, T]`. -/
theorem fwdMap_mem_H_of_notMem {W : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T) (hW : ContinuousOn W (Icc 0 T)) {z : ℂ}
    (hz : z ∈ H) (hzK : z ∉ fwdHull W T) : fwdMap W T z ∈ H := by
  have hsol := exists_isForwardSol_of_not_mem_fwdHull hT hz hzK
  have hc := Ito.mem_diff_fwdHull_clampDrv hT hW hz hsol
  have h := Thm11Asm.MeasCont.fwdMap_im_pos_of_not_mem_fwdHull (Ito.continuous_clampDrv hT hW) hz hT hc.2
    ⟨hT, le_rfl⟩
  rw [Ito.fwdMap_clampDrv_of_le le_rfl] at h
  exact h

/-- A lifetime whose killed driving is measurable is measurable. -/
theorem measurable_of_isMeasurableKilledDriving {Ω : Type u} [MeasurableSpace Ω] {nL nR : ℕ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hX : IsMeasurableKilledDriving W VL VR V) : Measurable V := by
  refine measurable_of_Ioi fun x => ?_
  induction x using ENNReal.recTopCoe with
  | top =>
    have e : V ⁻¹' Ioi ⊤ = ∅ := by ext ω; simp
    rw [e]; exact MeasurableSet.empty
  | coe r =>
    have e : V ⁻¹' Ioi (r : ℝ≥0∞) =
        {ω | (r : ℝ≥0∞) < V ω ∧ (W r ω, fun i => VL i r ω, fun i => VR i r ω) ∈ univ} := by
      ext ω; simp
    rw [e]; exact hX r univ MeasurableSet.univ

end Aux

/-! ### The interface -/

/-- **A coupling through the stop `V` with a full evolution** (WFS-0): a full integrated evolution
`(W, V^{·,L}, V^{·,R}, B, ζ)` (Definition 2.1), a stop `V ≤ ζ`, a measurable field `h` with `h − 𝔥⁰` a zero-boundary
GFF, and the clauses of the frozen `IsOptionalHullCoupling` (local hull; conditional law off the hull given the stopped
σ-algebra) at every stopping time `τ` of the driving filtration of the coordinates killed at `V` with `τ < V` almost
surely. -/
def IsCouplingThrough (κ : ℝ) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
    (ζ V : Ω → ℝ≥0∞) (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) : Prop :=
  IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ ∧ (∀ ω, V ω ≤ ζ ω) ∧ Measurable h ∧
    (∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR)
        (forceJumpSet xL xR) u₀ →
      LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => h ω φ - ∫ z, u₀ z * φ z) P) ∧
    ∃ hX : IsMeasurableKilledDriving W VL VR V,
      ∀ (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime (drivingFiltration P hX) τ),
        (∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < V ω) →
        IsLocalSet (fun ω => QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal ω)
            ((τ ω).untopD 0 : ℝ≥0)) h P ∧
          ∀ u : Ω → ℂ → ℝ,
            (∀ ω, IsBoundedHarmonicExtension
                (forceBoundaryData κ ρL ρR (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
                  (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω))
                (forceJumpSet (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
                  (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω))
                (u ω)) →
            ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
              Disjoint (tsupport φ) (QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal ω)
                  ((τ ω).untopD 0 : ℝ≥0)) →
                condExp hτ.measurableSpace P
                    (fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ))) ω =
                  Complex.exp (Complex.I * ((∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω)
                      ((τ ω).untopD 0 : ℝ≥0) (u ω) z * φ z : ℝ) : ℂ) -
                    (((1 / 2 : ℝ) * loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω)
                      ((τ ω).untopD 0 : ℝ≥0) φ : ℝ) : ℂ))


/-! ### Derivation from a stopped coupling on a continuation -/

section Derive

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **A stopped coupling read on a continuation is a coupling through the stop** (WFS-0). Let `(W, V^{·,L}, V^{·,R},
V, h)` be a coupling through `V` on `(Ω, P)` (`IsStoppedHullCoupling`) and let `(W', V'^{·,L}, V'^{·,R}, B', ζ')` be a
full integrated evolution on `(Ω', P')`, `P'.map π = P`, with `V ∘ π ≤ ζ'` and the same coordinates before `V ∘ π`.
Then `(W', …, ζ')` with the stop `V ∘ π ∧ ζ'` (almost surely `V ∘ π`) and the field `h ∘ π` is a coupling through the
stop. -/
theorem isCouplingThrough_of_continuation {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hSC : IsStoppedHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B V h)
    {Ω' : Type u} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P'] {π : Ω' → Ω}
    (hπ : Measurable π) (hπP : P'.map π = P) {𝓕' : Filtration ℝ≥0 mΩ'} {W' : ℝ≥0 → Ω' → ℝ}
    {VL' : Fin nL → ℝ≥0 → Ω' → ℝ} {VR' : Fin nR → ℝ≥0 → Ω' → ℝ} {B' : ℝ≥0 → Ω' → ℝ} {ζ' : Ω' → ℝ≥0∞}
    (hE' : IsIntegratedSLEEvolution κ xL xR ρL ρR P' 𝓕' W' VL' VR' B' ζ')
    (hag : ∀ᵐ p ∂P', V (π p) ≤ ζ' p ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < V (π p) →
      W' t p = W t (π p) ∧ (∀ i, VL' i t p = VL i t (π p)) ∧ ∀ j, VR' j t p = VR j t (π p)) :
    IsCouplingThrough κ xL xR ρL ρR P' 𝓕' W' VL' VR' B' ζ' (fun p => min (V (π p)) (ζ' p))
      (fun p => h (π p)) := by
  classical
  obtain ⟨-, -, hhm, hgff, hXV, hcl⟩ := hSC
  have hVm : Measurable V := measurable_of_isMeasurableKilledDriving hXV
  have hX' := Coupling.IsIntegratedSLEEvolution.isMeasurableKilledDriving hE'
  set V' : Ω' → ℝ≥0∞ := fun p => min (V (π p)) (ζ' p) with hV'
  -- the driving killed at `V'`
  have hXV' : IsMeasurableKilledDriving W' VL' VR' V' := by
    intro r A hA
    have e : {p | (r : ℝ≥0∞) < V' p ∧ (W' r p, fun i => VL' i r p, fun i => VR' i r p) ∈ A} =
        π ⁻¹' {ω | (r : ℝ≥0∞) < V ω ∧ (W r ω, fun i => VL i r ω, fun i => VR i r ω) ∈ univ} ∩
          {p | (r : ℝ≥0∞) < ζ' p ∧ (W' r p, fun i => VL' i r p, fun i => VR' i r p) ∈ A} := by
      ext p
      simp only [hV', mem_ofPred_eq, lt_min_iff, mem_inter_iff, mem_preimage, mem_univ, and_true]
      tauto
    rw [e]
    exact (hπ (hXV r univ MeasurableSet.univ)).inter (hX' r A hA)
  have hag' : ∀ᵐ p ∂P', V' p = V (π p) ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < V (π p) →
      W' t p = W t (π p) ∧ (∀ i, VL' i t p = VL i t (π p)) ∧ ∀ j, VR' j t p = VR j t (π p) := by
    filter_upwards [hag] with p ⟨h1, h2⟩
    exact ⟨min_eq_left h1, h2⟩
  -- the driving filtration killed at `V'` is the augmented pull-back
  have hfilt : drivingFiltration P' hXV' =
      usualAugmentation (filtrationComap π hπ (killedDrivingFiltration hXV)) P' := by
    rw [← drivingFiltration_comp hXV hπ P']
    refine drivingFiltration_congr_ae hXV' _ ?_
    filter_upwards [hag'] with p ⟨h1, h2⟩
    refine ⟨h1.symm, fun t ht => ?_⟩
    rw [h1] at ht
    obtain ⟨a, b, c⟩ := h2 t ht
    exact ⟨a.symm, fun i => (b i).symm, fun j => (c j).symm⟩
  refine ⟨hE', fun p => min_le_right _ _, hhm.comp hπ, fun u₀ hu₀ => ?_, hXV', fun τ hτ hτV => ?_⟩
  · have h0 := hgff u₀ hu₀
    rw [← hπP] at h0
    exact Restart.isZBGFFProcess_comp hπ h0
  -- a stopping time is almost surely read through `π`
  have hτ' : IsStoppingTime (usualAugmentation (filtrationComap π hπ (killedDrivingFiltration hXV)) P') τ := by
    rw [← hfilt]; exact hτ
  have hfin : ∀ᵐ p ∂P', τ p ≠ ⊤ := by
    filter_upwards [hτV] with p hp htop
    rw [htop] at hp
    exact absurd hp (not_lt.2 le_top)
  obtain ⟨s, hs, hτs⟩ := exists_isStoppingTime_ae_eq_comp hπ hπP hτ' hfin
  have hs' : IsStoppingTime (drivingFiltration P hXV) (fun x => (s x : WithTop ℝ≥0)) := hs
  have hsm : Measurable s := QuantumZipper.StrongMarkov.measurable_of_isStoppingTime hs
  have hgood : ∀ᵐ p ∂P', τ p = (s (π p) : WithTop ℝ≥0) ∧ (s (π p) : ℝ≥0∞) < V (π p) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < V (π p) →
        W' t p = W t (π p) ∧ (∀ i, VL' i t p = VL i t (π p)) ∧ ∀ j, VR' j t p = VR j t (π p) := by
    filter_upwards [hτs, hτV, hag'] with p h1 h2 ⟨h3, h4⟩
    refine ⟨h1, ?_, h4⟩
    have h5 : (τ p : ℝ≥0∞) = (s (π p) : ℝ≥0∞) := by rw [h1]; rfl
    rw [← h5, ← h3]
    exact h2
  have hsV : ∀ᵐ ω ∂P, (s ω : ℝ≥0∞) < V ω := by
    have hS : MeasurableSet {ω | (s ω : ℝ≥0∞) < V ω} :=
      measurableSet_lt (measurable_coe_nnreal_ennreal.comp hsm) hVm
    rw [← hπP, ae_map_iff hπ.aemeasurable hS]
    filter_upwards [hgood] with p hp
    exact hp.2.1
  obtain ⟨hloc, hform⟩ := hcl (fun x => (s x : WithTop ℝ≥0)) hs'
    (hsV.mono fun ω hω => ⟨hω.le, WithTop.coe_ne_top⟩)
  refine ⟨?_, fun u' hu' φ => ?_⟩
  · -- the local-set clause
    refine IsLocalSet.congr_ae (isLocalSet_comp hloc hπ hπP) ?_
    filter_upwards [hgood] with p ⟨h1, h2, h3⟩
    rw [h1]
    simp only [WithTop.untopD_coe]
    exact fwdHull_eq_of_agree (fun t ht => (h3 t ht).1) h2
  -- the conditional-law clause: the stopped coupling's clause with the chosen extensions
  set dL : Ω → Fin nL → ℝ := fun ω i => VL i (s ω) ω - W (s ω) ω with hdL
  set dR : Ω → Fin nR → ℝ := fun ω j => VR j (s ω) ω - W (s ω) ω with hdR
  have hex := fun ω => Spec.Provider.existsUnique_isBoundedHarmonicExtension_forceBoundaryData (κ := κ)
    (ρL := ρL) (ρR := ρR) (vL := dL ω) (vR := dR ω)
  set u : Ω → ℂ → ℝ := fun ω => (hex ω).choose with hudef
  have hold := hform u (fun ω => by simp only [WithTop.untopD_coe]; exact (hex ω).choose_spec.1) φ
  have hold' : ∀ᵐ p ∂P', Disjoint (tsupport φ) (QuantumZipper.fwdHull (fun r : ℝ => W r.toNNReal (π p))
        (((s (π p) : WithTop ℝ≥0)).untopD 0 : ℝ≥0)) →
      condExp hs'.measurableSpace P (fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ))) (π p) =
        Complex.exp (Complex.I * ((∫ z, couplingMean κ (fun r : ℝ => W r.toNNReal (π p))
            (((s (π p) : WithTop ℝ≥0)).untopD 0 : ℝ≥0) (u (π p)) z * φ z : ℝ) : ℂ) -
          (((1 / 2 : ℝ) * loewnerGreenEnergy (fun r : ℝ => W r.toNNReal (π p))
            (((s (π p) : WithTop ℝ≥0)).untopD 0 : ℝ≥0) φ : ℝ) : ℂ)) := by
    have hq : Measure.QuasiMeasurePreserving π P' P := ⟨hπ, hπP.le.absolutelyContinuous⟩
    exact hq.ae hold
  set g : Ω → ℂ := fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) with hgdef
  have hgm : Measurable g := Complex.measurable_exp.comp (measurable_const.mul
    (Complex.measurable_ofReal.comp ((Sobolev.measurable_distOn_apply φ).comp hhm)))
  have hgi : Integrable g P := Integrable.of_bound hgm.aestronglyMeasurable 1
    (ae_of_all _ fun ω => by simp only [hgdef, Complex.norm_exp_I_mul_ofReal, le_refl])
  have hce := condExp_comp_ae_eq hπ hπP hs hτ' hτs hgi
  have hσ : hτ.measurableSpace = hτ'.measurableSpace := measurableSpace_congr hfilt hτ hτ'
  have hcont : ∀ᵐ p ∂P', ContinuousOn (fun t => W' t p) {t : ℝ≥0 | (t : ℝ≥0∞) < ζ' p} := by
    filter_upwards [hE'.2.2.2.2] with p hp
    exact hp.2.2.2.1
  filter_upwards [hold', hce, hgood, hcont, hag] with p hp hcp ⟨h1, h2, h3⟩ hcp' ⟨hVζ, _⟩ hdisj
  have hτp : ((τ p).untopD 0 : ℝ≥0) = s (π p) := by rw [h1, WithTop.untopD_coe]
  have hhull := fwdHull_eq_of_agree (fun t ht => (h3 t ht).1) h2
  have hEq : EqOn (fun r : ℝ => W r.toNNReal (π p)) (fun r : ℝ => W' r.toNNReal p) (Icc 0 (s (π p) : ℝ)) :=
    eqOn_Icc_of_agree (fun t ht => (h3 t ht).1) h2
  rw [hτp, hhull] at hdisj
  have hdisj' : Disjoint (tsupport φ) (QuantumZipper.fwdHull (fun r : ℝ => W r.toNNReal (π p))
      (((s (π p) : WithTop ℝ≥0)).untopD 0 : ℝ≥0)) := by rw [WithTop.untopD_coe]; exact hdisj
  have hval := hp hdisj'
  simp only [WithTop.untopD_coe] at hval
  -- the extensions agree on `ℍ`
  have hW3 := h3 (s (π p)) h2
  have hu'p : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR (dL (π p)) (dR (π p)))
      (forceJumpSet (dL (π p)) (dR (π p))) (u' p) := by
    have hb := hu' p
    rw [hτp] at hb
    have e1 : (fun i => VL' i (s (π p)) p - W' (s (π p)) p) = dL (π p) := funext fun i => by
      simp only [hdL, hW3.1, hW3.2.1 i]
    have e2 : (fun j => VR' j (s (π p)) p - W' (s (π p)) p) = dR (π p) := funext fun j => by
      simp only [hdR, hW3.1, hW3.2.2 j]
    rw [e1, e2] at hb
    exact hb
  have hEqH : EqOn (u' p) (u (π p)) H := (hex (π p)).choose_spec.2 (u' p) hu'p
  -- continuity of the driver on `[0, s]`
  have hsζ : (s (π p) : ℝ≥0∞) < ζ' p := lt_of_lt_of_le h2 hVζ
  have hcW' : ContinuousOn (fun r : ℝ => W' r.toNNReal p) (Icc 0 (s (π p) : ℝ)) := by
    refine hcp'.comp continuous_real_toNNReal.continuousOn fun r hr => ?_
    exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr.2)) hsζ
  have hcW : ContinuousOn (fun r : ℝ => W r.toNNReal (π p)) (Icc 0 (s (π p) : ℝ)) := hcW'.congr hEq
  have hint : (∫ z, couplingMean κ (fun r : ℝ => W' r.toNNReal p) (s (π p)) (u' p) z * φ z) =
      ∫ z, couplingMean κ (fun r : ℝ => W r.toNNReal (π p)) (s (π p)) (u (π p)) z * φ z := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    dsimp only
    by_cases hz : φ z = 0
    · simp only [hz, mul_zero]
    · have hzt : z ∈ tsupport φ := subset_tsupport _ hz
      have hzH : z ∈ H := φ.tsupport_subset hzt
      have hzK : z ∉ QuantumZipper.fwdHull (fun r : ℝ => W r.toNNReal (π p)) (s (π p)) :=
        fun hK => Set.disjoint_left.1 hdisj hzt hK
      have hf := fwdMap_mem_H_of_notMem (NNReal.coe_nonneg (s (π p))) hcW hzH hzK
      rw [← Sec7.Lemma71B.couplingMean_congr (NNReal.coe_nonneg (s (π p))) hEq κ (u' p) z]
      simp only [couplingMean, hEqH hf]
  have hval2 : P[g | hs.measurableSpace] (π p) =
      Complex.exp (Complex.I * ((∫ z, couplingMean κ (fun r : ℝ => W r.toNNReal (π p))
          (s (π p)) (u (π p)) z * φ z : ℝ) : ℂ) -
        (((1 / 2 : ℝ) * loewnerGreenEnergy (fun r : ℝ => W r.toNNReal (π p)) (s (π p)) φ : ℝ) : ℂ)) := hval
  rw [hσ, hcp, hval2, hτp, loewnerGreenEnergy_congr hEq, hint]

/-- **Every stopped coupling is, on a continuation, a coupling through its stop** (WFS-0 with (CONT), `κ > 0`): on an
enlargement `π : Ω' → Ω` with `P'.map π = P` there is a full integrated evolution, agreeing with the stopped coordinates
before `V ∘ π ≤ ζ'`, that with the stop `V ∘ π ∧ ζ'` and the field `h ∘ π` is a coupling through the stop. -/
theorem exists_isCouplingThrough (hκ : 0 < κ) (hF : IsOrderedForceWord xL xR) {Ω : Type u}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {V : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hSC : IsStoppedHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B V h) :
    ∃ (Ω' : Type u) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P') (π : Ω' → Ω)
      (_ : Measurable π) (𝓕' : Filtration ℝ≥0 mΩ') (W' : ℝ≥0 → Ω' → ℝ) (VL' : Fin nL → ℝ≥0 → Ω' → ℝ)
      (VR' : Fin nR → ℝ≥0 → Ω' → ℝ) (B' : ℝ≥0 → Ω' → ℝ) (ζ' : Ω' → ℝ≥0∞),
      P'.map π = P ∧
      IsCouplingThrough κ xL xR ρL ρR P' 𝓕' W' VL' VR' B' ζ' (fun p => min (V (π p)) (ζ' p))
        (fun p => h (π p)) ∧
      ∀ᵐ p ∂P', V (π p) ≤ ζ' p ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < V (π p) →
        W' t p = W t (π p) ∧ (∀ i, VL' i t p = VL i t (π p)) ∧ ∀ j, VR' j t p = VR j t (π p) := by
  obtain ⟨Ω', mΩ', P', hP', π, hπ, 𝓕', W', VL', VR', B', ζ', hπP, hE', hag⟩ :=
    StoppedCont.stoppedContinuationStatement hκ xL xR ρL ρR hF P 𝓕 W VL VR B V hSC.1 hSC.2.1
  exact ⟨Ω', mΩ', P', hP', π, hπ, 𝓕', W', VL', VR', B', ζ', hπP,
    isCouplingThrough_of_continuation hSC hπ hπP hE' hag, hag⟩

end Derive

end WFS

end InteractingSLE
