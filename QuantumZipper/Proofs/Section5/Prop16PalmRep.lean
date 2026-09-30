import QuantumZipper.Proofs.Section5.Prop16NodeB2Rep
import QuantumZipper.Proofs.Section5.Prop16NodeCMaskLaw
import QuantumZipper.Proofs.Section5.Prop16ShiftGoodPalm
import QuantumZipper.Proofs.Section5.Prop16D4WInSc0

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, node B′: the representation node `Prop16PalmRepStmt` (P16-PALMREP)

`prop16PalmRepStmt_holds : Prop16PalmRepStmt`, with no hypotheses.

* **Coordinates.** `μ_j` is the `j`-th dyadic folded circle when that circle is admissible and
  carried by a compact subset of `D ∪ (a,b)` (`LocAdm`), and `0` otherwise (`0` is `LocAdm`).
* **Reading.** `repRead γ C … F (y, t)` subtracts the deterministic `∫ 𝔥₀ dμ_j` from the raw
  readings, rebuilds a field sample (`reconstruct`), zooms at `t` (with `F t` in place of
  `𝔥₀(t)`, `F` a measurable version of `𝔥₀` on `(a,b)`), reads the local scale through the
  measurable proxy `Meas.M` (rational radii), rescales and masks. It is jointly measurable in `(y, t)`.
* **Exactness.** For any field `Y` whose readings are `y` on the local circles, and whose zoom at
  `t ∈ (a,b)` has a genuine local area measure on `D − t`, `repRead (y, t)` equals the masked
  canonical coordinates of `Y` at `t` (`repRead_eq_of_agree`). Locality comes from
  `palmCanonMask_congr`. The rebuilt field agrees with `Y` on every dyadic folded circle inside
  the open set `W` with `W ∩ Hbar = D ∪ (a,b)`.
* **Goodness a.s.** Under `prop16Q` this is local niceness (`prop16_hloc`, `exists_limit_of_agree`).
  For the Palm-shifted field at a fixed `x ∈ (a,b)` it is `prop16PalmShiftGoodStmt_proved`.

Source: Sheffield, arXiv:1012.4797, proof of Prop. 1.6 (p. 25). The zoom reads the field only in
`D` near the boundary point, so the zoomed data are a function of countably many local
circle averages. No published counterpart exists for the measurability bookkeeping. It is an own
elementary argument that follows the project's `palmMaskRead` (`Prop16NodeCMaskLaw.lean`) and
`aemeasurable_zoomFree_scale` (`Prop16D4WInSc0.lean`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Asm

open TV Factorization Prop16Area Prop16Area.Meas LQGMeas

/-- The `i`-th dyadic folded circle. -/
abbrev fcI (i : ℕ) : Measure ℂ := foldedCircle (dyadicIndex i).1 (radius (dyadicIndex i).2)

open Classical in
/-- The representing coordinate measures: the local dyadic folded circles (else `0`). -/
def repMeas (D : Set ℂ) (a b : ℝ) (j : ℕ) : Measure ℂ :=
  if LocAdm D a b (fcI j) then fcI j else 0

open Classical in
/-- Field readings on the local circles, recovered from the raw readings of `𝔥₀ + field`. -/
def repAdj (D : Set ℂ) (a b : ℝ) (h0 : ℂ → ℝ) (y : ℕ → ℝ) : ℕ → ℝ :=
  fun i => if LocAdm D a b (fcI i) then y i - ∫ z, h0 z ∂(fcI i) else 0

/-- The field rebuilt from the raw readings. -/
def repFam (D : Set ℂ) (a b : ℝ) (h0 : ℂ → ℝ) (y : ℕ → ℝ) : FieldSample :=
  reconstruct (repAdj D a b h0 y)

section Defs

variable (γ C : ℝ) (D : Set ℂ) (a b : ℝ) (h0 : ℂ → ℝ) (F : ℝ → ℝ)

/-- The zoomed rebuilt field at `p = (y, t)` (with `F t` for `𝔥₀(t)`). -/
def repZoom (p : (ℕ → ℝ) × ℝ) : FieldSample :=
  addConst (zoomField γ C (repFam D a b h0 p.1) p.2) (F p.2)

/-- Its reconstruction from coordinates. -/
def repZr (p : (ℕ → ℝ) × ℝ) : FieldSample := recon (repZoom γ C D a b h0 F p)

/-- The cut-offs of `D − t`. -/
def repPhi : ℕ → (ℕ → ℝ) × ℝ → ℂ → ℝ := fun n p z => openBump D n (z + (p.2 : ℂ))

/-- The measurable scale proxy. -/
def repScaleProxy (p : (ℕ → ℝ) × ℝ) : ℝ :=
  sInf {s : ℝ | 0 < s ∧ ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) ≤ s ∧
    1 ≤ M γ (repZr γ C D a b h0 F) (repPhi D) p q}

/-- **The measurable reading** `Φ_C`. -/
def repRead (p : (ℕ → ℝ) × ℝ) : ℕ → ℝ :=
  maskCoords D a b (repScaleProxy γ C D a b h0 F p) p.2
    (coords (rescale (reconstruct (coords (repZoom γ C D a b h0 F p))) (Qc γ)
      (repScaleProxy γ C D a b h0 F p)))

end Defs

variable {γ C : ℝ} {D : Set ℂ} {a b : ℝ} {h0 : ℂ → ℝ} {F : ℝ → ℝ}

theorem locAdm_zero_rep (D : Set ℂ) (a b : ℝ) : LocAdm D a b 0 := by
  refine ⟨⟨inferInstance, ⟨∅, isCompact_empty, empty_subset _, by simp⟩, 0, by simp,
    fun y => by simp⟩, ∅, isCompact_empty, empty_subset _, by simp⟩

theorem locAdm_repMeas (D : Set ℂ) (a b : ℝ) (j : ℕ) : LocAdm D a b (repMeas D a b j) := by
  classical
  unfold repMeas
  split_ifs with h
  · exact h
  · exact locAdm_zero_rep D a b

theorem measurable_repAdj : Measurable (repAdj D a b h0) := by
  classical
  refine measurable_pi_iff.2 fun i => ?_
  by_cases h : LocAdm D a b (fcI i)
  · simp only [repAdj, h, if_true]
    exact (measurable_pi_apply i).sub measurable_const
  · simp only [repAdj, h, if_false]
    exact measurable_const

theorem measurable_coords_repZoom (hF : Measurable F) :
    Measurable fun p : (ℕ → ℝ) × ℝ => coords (repZoom γ C D a b h0 F p) := by
  have hR : ∀ μ : Measure ℂ, Measurable fun y : ℕ → ℝ => repFam D a b h0 y μ := fun μ =>
    (measurable_pi_apply μ).comp (measurable_reconstruct.comp measurable_repAdj)
  have e0 : ∀ y, ofFun (fun _ => (0 : ℝ)) + repFam D a b h0 y = repFam D a b h0 y :=
    fun y => by funext μ; simp [ofFun]
  have hZ : Measurable fun p : (ℕ → ℝ) × ℝ => coords (zoomField γ C (repFam D a b h0 p.1) p.2) := by
    have := measurable_coords_zoomField γ C (fun _ => (0 : ℝ)) hR
    simpa only [e0] using this
  refine measurable_pi_iff.2 fun i => ?_
  have e : (fun p : (ℕ → ℝ) × ℝ => coords (repZoom γ C D a b h0 F p) i) = fun p =>
      coords (zoomField γ C (repFam D a b h0 p.1) p.2) i +
        F p.2 * ((foldedCircle (dyadicIndex i).1 (radius (dyadicIndex i).2)) univ).toReal := by
    funext p; rfl
  rw [e]
  exact ((measurable_pi_apply i).comp hZ).add ((hF.comp measurable_snd).mul measurable_const)

theorem isBumpFamily_repPhi (hDo : IsOpen D) (hDH : D ⊆ H) :
    IsBumpFamily (fun p : (ℕ → ℝ) × ℝ => zoomDomain D p.2) (repPhi D) := by
  have hDc : Dᶜ.Nonempty := ⟨0, fun h => by simpa [H] using hDH h⟩
  exact isBumpFamily_comp (α := (ℕ → ℝ) × ℝ) hDo hDc (g := fun p z => z + (p.2 : ℂ))
    (by fun_prop) (fun _ => by fun_prop)

theorem measurable_repScaleProxy (hF : Measurable F) (hDo : IsOpen D) (hDH : D ⊆ H) :
    Measurable (repScaleProxy γ C D a b h0 F) := by
  have hM := fun q : ℚ => measurable_M (γ := γ)
    (measurable_reconstruct.comp (measurable_coords_repZoom (γ := γ) (C := C) (D := D) (a := a)
      (b := b) (h0 := h0) hF) : Measurable (repZr γ C D a b h0 F))
    (isBumpFamily_repPhi hDo hDH) (q : ℝ)
  refine LQGMeas.measurable_sInf_upClosed _ (fun r => ?_) (fun v s t hs hst => ?_)
    (fun v s hs => hs.1)
  · have e : {v : (ℕ → ℝ) × ℝ | (r : ℝ) ∈ {s : ℝ | 0 < s ∧ ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) ≤ s ∧
        1 ≤ M γ (repZr γ C D a b h0 F) (repPhi D) v q}} =
        {_v | 0 < (r : ℝ)} ∩ ⋃ q : ℚ, ({_v | 0 < (q : ℝ) ∧ (q : ℝ) ≤ r} ∩
          {v | 1 ≤ M γ (repZr γ C D a b h0 F) (repPhi D) v q}) := by
      ext v; simp only [mem_setOf_eq, mem_inter_iff, mem_iUnion, and_assoc]
    rw [e]
    exact (MeasurableSet.const _).inter (MeasurableSet.iUnion fun q =>
      (MeasurableSet.const _).inter (measurableSet_le measurable_const (hM q)))
  · obtain ⟨h1, q, hq0, hqs, hq⟩ := hs
    exact ⟨lt_of_lt_of_le h1 hst, q, hq0, hqs.trans hst, hq⟩

theorem measurable_repRead (hF : Measurable F) (hDo : IsOpen D) (hDH : D ⊆ H) :
    Measurable (repRead γ C D a b h0 F) := by
  have hs := measurable_repScaleProxy (γ := γ) (C := C) (a := a) (b := b) (h0 := h0) hF hDo hDH
  exact (measurable_maskCoords D a b).comp (hs.prodMk (measurable_snd.prodMk
    ((measurable_coords_rescale_reconstruct (Qc γ)).comp
      ((measurable_coords_repZoom hF).prodMk hs))))

/-- **On the good event the reading is exact.** -/
theorem repRead_eq (hDo : IsOpen D) (hDH : D ⊆ H) {p : (ℕ → ℝ) × ℝ} (hFp : F p.2 = h0 p.2)
    (hv : p ∈ goodSet γ (repZr γ C D a b h0 F) fun p => zoomDomain D p.2) :
    repRead γ C D a b h0 F p = palmCanonMask γ C D a b h0 (repFam D a b h0) p := by
  have hz : repZoom γ C D a b h0 F p = zoomFree γ C h0 (repFam D a b h0) p := by
    simp only [repZoom, zoomFree, hFp]
  have hsc : repScaleProxy γ C D a b h0 F p = palmScale γ C D h0 (repFam D a b h0) p := by
    unfold repScaleProxy
    have e : ∀ q : ℚ, M γ (repZr γ C D a b h0 F) (repPhi D) p q =
        qAreaMeasureOn γ (repZr γ C D a b h0 F p) (zoomDomain D p.2) (hb q) := fun q =>
      (measure_eq_M (isBumpFamily_repPhi hDo hDH) hv q).symm
    simp_rw [e]
    have := sInf_rat_upClosure_eq
      {s : ℝ | 0 < s ∧ 1 ≤ qAreaMeasureOn γ (repZr γ C D a b h0 F p) (zoomDomain D p.2) (hb s)}
      (fun s t hs hst => ⟨lt_of_lt_of_le hs.1 hst, hs.2.trans (measure_mono
        (inter_subset_inter_left _ (Metric.ball_subset_ball hst)))⟩) (fun s hs => hs.1)
    simp only [mem_setOf_eq] at this
    rw [show (fun s : ℝ => 0 < s ∧ ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) ≤ s ∧
        1 ≤ qAreaMeasureOn γ (repZr γ C D a b h0 F p) (zoomDomain D p.2) (hb q)) =
        fun s => 0 < s ∧ ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) ≤ s ∧ 0 < (q : ℝ) ∧
        1 ≤ qAreaMeasureOn γ (repZr γ C D a b h0 F p) (zoomDomain D p.2) (hb q) from by
      funext s; apply propext; constructor
      · rintro ⟨h1, q, h2, h3, h4⟩; exact ⟨h1, q, h2, h3, h2, h4⟩
      · rintro ⟨h1, q, h2, h3, -, h4⟩; exact ⟨h1, q, h2, h3, h4⟩]
    rw [this]
    show scaleParamOn γ (recon (repZoom γ C D a b h0 F p)) _ = _
    rw [scaleParamOn_recon, hz]
    rfl
  show maskCoords D a b _ p.2 _ = maskCoords D a b _ p.2 _
  rw [hsc]
  congr 1
  show _ = coords (canonicalOn γ _ _)
  unfold canonicalOn
  rw [rescale_reconstruct_coords, hz]
  rfl

/-- The rebuilt field agrees with `Y` on the dyadic circles inside `W`. -/
theorem circAgree_repFam {W : Set ℂ} (hWV : W ∩ Hbar = D ∪ realSet (Ioo a b)) (Y : FieldSample)
    (y : ℕ → ℝ) (hy : ∀ i, LocAdm D a b (fcI i) → y i = ∫ z, h0 z ∂(fcI i) + Y (fcI i)) :
    Prop16Area.G.CircAgree W Y (repFam D a b h0 y) := by
  classical
  intro n k z hz hW
  have hex : ∃ i, foldedCircle (dyadicIndex i).1 (radius (dyadicIndex i).2) =
      foldedCircle (dyadicRoundC n z) (radius k) := by
    obtain ⟨i, hi⟩ := dyadicIndex_surj n k z
    exact ⟨i, by rw [hi]⟩
  have hc := CircleCont.dyadicRoundC_mem_Hbar hz n
  have hloc : LocAdm D a b (foldedCircle (dyadicRoundC n z) (radius k)) := by
    refine ⟨isAdmissibleH_foldedCircle hc (radius_pos k), closedBall (dyadicRoundC n z) (radius k)
      ∩ Hbar, Prop16Area.G.isCompact_closedBall_inter_Hbar _ _, fun w hw => ?_, ?_⟩
    · rw [← hWV]; exact ⟨hW hw, hw.2⟩
    · exact ae_iff.1 (Prop16Area.G.ae_fc_mem_ball_inter hc (radius_pos k))
  unfold repFam reconstruct
  rw [dif_pos hex]
  have hj := Nat.find_spec hex
  have hA : LocAdm D a b (fcI (Nat.find hex)) := by
    show LocAdm D a b (foldedCircle _ _); rw [hj]; exact hloc
  simp only [repAdj, hA, if_true, hy _ hA, add_sub_cancel_left]
  exact congrArg Y hj.symm

/-- **Exactness for any field agreeing with the readings, given a local area measure.** -/
theorem repRead_eq_of_agree (hDo : IsOpen D) (hDH : D ⊆ H) {W : Set ℂ} (hWo : IsOpen W)
    (hWV : W ∩ Hbar = D ∪ realSet (Ioo a b)) {Ω' : Type} (Y : Ω' → FieldSample) (ω : Ω') (t : ℝ)
    (y : ℕ → ℝ) (ht : F t = h0 t)
    (hy : ∀ i, LocAdm D a b (fcI i) → y i = ∫ z, h0 z ∂(fcI i) + Y ω (fcI i))
    (hgood : ∃ m, IsVagueLimitOn (zoomDomain D t) (areaApprox γ (zoomFree γ C h0 Y (ω, t))) m) :
    palmCanonMask γ C D a b h0 Y (ω, t) = repRead γ C D a b h0 F (y, t) := by
  have hVW : D ∪ realSet (Ioo a b) ⊆ W := fun z hz => by
    have : z ∈ W ∩ Hbar := by rw [hWV]; exact hz
    exact this.1
  have hWto : IsOpen ((fun z => z + (t : ℂ)) ⁻¹' W) :=
    hWo.preimage (continuous_id.add continuous_const)
  have hag := circAgree_repFam (h0 := h0) hWV (Y ω) y hy
  have e1 : palmCanonMask γ C D a b h0 Y (ω, t) =
      palmCanonMask γ C D a b h0 (repFam D a b h0) (y, t) :=
    palmCanonMask_congr hWo hDo hDH hVW Y (repFam D a b h0) ω y t hag
  have hg : (y, t) ∈ goodSet γ (repZr γ C D a b h0 F) fun p => zoomDomain D p.2 := by
    obtain ⟨m, hm⟩ := hgood
    show ∃ m, IsVagueLimitOn (zoomDomain D t) (areaApprox γ (repZr γ C D a b h0 F (y, t))) m
    have hz : repZoom γ C D a b h0 F (y, t) = zoomFree γ C h0 (repFam D a b h0) (y, t) := by
      simp only [repZoom, zoomFree, ht]
    rw [repZr, areaApprox_recon, hz]
    have h' : Prop16Area.G.CircAgree ((fun z => z + (t : ℂ)) ⁻¹' W)
        (zoomFree γ C h0 (repFam D a b h0) (y, t)) (zoomFree γ C h0 Y (ω, t)) :=
      circAgree_zoomFree_nc hWo (circAgree_symm_nc hag) γ C (h0 t) t
    exact ⟨m, Prop16Area.G.isVagueLimitOn_of_circAgree hWto h' (zoomDomain_subset_H hDH t)
      (fun z hz => hVW (Or.inl hz)) hm⟩
  rw [e1, repRead_eq hDo hDH (p := (y, t)) ht hg]

/-- **Node B′, representation part (items (6), (7) of D30): proved.** -/
theorem prop16PalmRepStmt_holds : Prop16PalmRepStmt := by
  classical
  intro γ D c d a b h0 Ω _ P X hH _hmeas
  obtain ⟨hdat, hν, hnice⟩ := hH
  obtain ⟨hγ, hγ2, hgeo, hab, hca, hbd, hh0, hP, hX, -, hfin⟩ := id hdat
  obtain ⟨hDo, -, -, hDH, -⟩ := id hgeo
  obtain ⟨W, hWo, hWV⟩ := locGood_exists_open hgeo hca hbd
  set F : ℝ → ℝ := (Ioo a b).piecewise (fun s => h0 s) 0 with hFdef
  have hFm : Measurable F := by
    refine ContinuousOn.measurable_piecewise ?_ continuousOn_const measurableSet_Ioo
    exact hh0.comp Complex.continuous_ofReal.continuousOn fun s hs => Or.inr ⟨s, hs, rfl⟩
  refine ⟨repMeas D a b, fun C => repRead γ C D a b h0 F, locAdm_repMeas D a b,
    fun C => measurable_repRead hFm hDo hDH, fun C => ?_, fun x hx C => ?_⟩
  · have hta : ∀ᵐ p ∂(prop16Q γ h0 a b P X), p.2 ∈ Ioo a b :=
      Prop16Area.G.ae_prop16Law_of_ae (G := fun _ t => t ∈ Ioo a b) (Prop16Area.G.aemeasurable_prop16Kernel' hν hfin)
        (fun ω => Prop16Area.G.sFinite_prop16Nu γ h0 a b (X ω)) (fun ω => Prop16Area.G.prop16Nu_compl_Ioo γ h0 a b (X ω))
        (ae_of_all _ fun _ _ ht => ht)
    have hlg : ∀ᵐ ω ∂P, Prop16Area.G.IsLocallyGoodOn γ (D ∪ realSet (Ioo a b)) (X ω) :=
      hnice.mono fun _ h => h.isLocallyGoodOn
    filter_upwards [hta, prop16_hloc hdat hν hlg C] with p hp hl
    obtain ⟨⟨W', hWo', hWV', y, ψ, hy, hψ, hag⟩, hUV, -⟩ := hl
    have hUo : IsOpen (zoomDomain D p.2) := hDo.preimage (continuous_id.add continuous_const)
    have hgood := Prop16Area.G.exists_limit_of_agree (γ := γ) hWo' hy (hWV' ▸ hψ) hag hUo
      (zoomDomain_subset_H hDH p.2)
      fun z hz => by have := hUV hz; rw [← hWV'] at this; exact this.1
    exact repRead_eq_of_agree hDo hDH hWo hWV X p.1 p.2 _
      (by simp only [hFdef, Set.piecewise_eq_of_mem _ _ _ hp])
      (fun i hi => by simp only [rawCoords, repMeas, hi, if_true]; rfl) hgood
  · filter_upwards [prop16PalmShiftGoodStmt_proved γ D c d a b h0 hγ hγ2 hgeo hab hca hbd P X hP
      hX hnice x hx C] with ω hω
    exact repRead_eq_of_agree hDo hDH hWo hWV (palmMixedField γ D (realSet (Icc c d)) X x) ω x _
      (by simp only [hFdef, Set.piecewise_eq_of_mem _ _ _ hx])
      (fun i hi => by simp only [palmRawCoords, repMeas, hi, if_true]; rfl) hω

end Prop16Asm

end QuantumZipper
