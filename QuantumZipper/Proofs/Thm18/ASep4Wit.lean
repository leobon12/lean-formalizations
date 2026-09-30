import QuantumZipper.Proofs.Thm18.ASep4Joint
import QuantumZipper.Proofs.Thm18.ASep3PsiRun
import QuantumZipper.Proofs.Thm18.ASepWitB

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP4 (step 3): the scale joint witness

Almost surely, for **every** scale `s > 0` and every time `t ≥ 0`, the unzipped rescaled field
`coordChange (rescale X Q s) f_t⁻¹ Q` is a regular sample (`ae_isRegularWith_rescale_all`).

On a box `(s, t) ∈ [a, b] × [0, n + 1]` the witness is
`G_{s,t}(c, ρ) = Y(t, c, s, ρ) + Q log s + Dfix W 0 0 Q (t, (c, ρ))`, `Y` the everywhere continuous
modification of `X((fc(c, ρ).map f_t⁻¹).map (s ·))` (`exists_contMod_νT_rescale'`):
* raw identity at countably many parameters: inner exactness `ae_tendsto_rescale_νT_fixed`;
* continuity in `(s, t)` of the raw values at dyadic circles: `ae_continuousOn_evalReg_rescale_box`
  and `continuousOn_Dfix`;
* commutation at countably many parameters: `ae_comm_Y5` (ASep4Comm) and `integral_Dfun_swap`;
* assembly: `forall_isRegularWith_of_joint_gen` (ASep4Joint).

This is the proof of `ae_exists_joint_witness_fixed` (ASepWitC) with the scale as an extra
parameter. Source: Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1 (through the cited
files); own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology

namespace QuantumZipper
namespace ASep

open RegCont CoordReg RegUnif GenUC

/-- Raw value of the unzipped rescaled field at a folded circle. -/
theorem coordChange_rescale_fc (x : FieldSample) {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) (Q s : ℝ) (c : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    coordChange (rescale x Q s) (fwdMapInv W t) Q (foldedCircle c ρ) =
      evalReg (rescale x Q s) (νT W c ρ t) + Dfix W 0 (fun _ => 0) Q (t, (c, ρ)) := by
  have e := integral_logAdd_eq_Dfix hW hW0 ht 0 (continuous_const (y := (0 : ℝ))) Q c hρ
  simp only [zero_mul, zero_add, integral_zero] at e
  show evalReg (rescale x Q s) ((foldedCircle c ρ).map (fwdMapInv W t)) +
    Q * ∫ z, Real.log ‖deriv (fwdMapInv W t) z‖ ∂foldedCircle c ρ = _
  rw [e]

theorem integral_add_const_add {μ : Measure ℂ} [IsProbabilityMeasure μ] {f g : ℂ → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (c : ℝ) :
    ∫ u, (f u + c + g u) ∂μ = ∫ u, f u ∂μ + c + ∫ u, g u ∂μ := by
  have e1 : ∫ u, (f u + c + g u) ∂μ = ∫ u, (f u + c) ∂μ + ∫ u, g u ∂μ :=
    integral_add (hf.add (integrable_const c)) hg
  have e2 : ∫ u, (f u + c) ∂μ = ∫ u, f u ∂μ + ∫ _u, c ∂μ := integral_add hf (integrable_const c)
  rw [e1, e2, integral_const]
  simp

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- The explicit scale witness built from a modification `Y` of the dilated pushed-circle
averages. -/
def witS (Y : (Fin 5 → ℝ) → Ω → ℝ) (W : ℝ → ℝ) (Q : ℝ) (ω : Ω) (st : ℝ × ℝ) (p : ℂ × ℝ) : ℝ :=
  Y (q5 st.2 p.1 st.1 p.2) ω + Q * Real.log st.1 + Dfix W 0 (fun _ => 0) Q (st.2, p)

/-- **Joint continuity of the scale witness.** -/
theorem continuousOn_witS {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    (Q : ℝ) {Y : (Fin 5 → ℝ) → Ω → ℝ} (ω : Ω)
    (hYc : ContinuousOn (fun q => Y q ω) {q | 0 < q 3 ∧ 0 < q 4}) :
    ContinuousOn (fun q : (ℝ × ℝ) × (ℂ × ℝ) => witS Y W Q ω q.1 q.2)
      ((Ioi 0 ×ˢ Icc 0 T) ×ˢ (Hbar ×ˢ Ioi 0)) := by
  have hDfc := continuousOn_Dfix hW hW0 hT 0 (continuous_const (y := (0 : ℝ))) Q
  have h1 : ContinuousOn (fun q : (ℝ × ℝ) × (ℂ × ℝ) => Y (q5 q.1.2 q.2.1 q.1.1 q.2.2) ω)
      ((Ioi 0 ×ˢ Icc 0 T) ×ˢ (Hbar ×ˢ Ioi 0)) :=
    hYc.comp (continuous_q5.comp (by fun_prop :
      Continuous fun q : (ℝ × ℝ) × (ℂ × ℝ) => (((q.1.2, q.2.1), q.1.1), q.2.2))).continuousOn
      fun q hq => ⟨hq.1.1, hq.2.2⟩
  have h2 : ContinuousOn (fun q : (ℝ × ℝ) × (ℂ × ℝ) => Q * Real.log q.1.1)
      ((Ioi 0 ×ˢ Icc 0 T) ×ˢ (Hbar ×ˢ Ioi 0)) :=
    continuousOn_const.mul (Real.continuousOn_log.comp (by fun_prop : Continuous
      fun q : (ℝ × ℝ) × (ℂ × ℝ) => q.1.1).continuousOn fun q hq =>
        (show (0 : ℝ) < q.1.1 from hq.1.1).ne')
  have h3 : ContinuousOn (fun q : (ℝ × ℝ) × (ℂ × ℝ) => Dfix W 0 (fun _ => 0) Q (q.1.2, q.2))
      ((Ioi 0 ×ˢ Icc 0 T) ×ˢ (Hbar ×ˢ Ioi 0)) :=
    hDfc.comp (by fun_prop : Continuous fun q : (ℝ × ℝ) × (ℂ × ℝ) => (q.1.2, q.2)).continuousOn
      fun q hq => ⟨hq.1.2, hq.2⟩
  exact (h1.add h2).add h3

/-- **The scale joint witness on one box**, for a given modification `Y`. -/
theorem ae_isRegularWith_rescale_box [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {W : ℝ → ℝ} (hWg : DrvGood W) (Q : ℝ) (n : ℕ) {α CH : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hCH : 0 ≤ CH)
    (hH : ∀ t ∈ Icc (0 : ℝ) ((n : ℝ) + 1), ∀ t' ∈ Icc (0 : ℝ) ((n : ℝ) + 1), |t - t'| ≤ 1 / 2 →
      |W t - W t'| ≤ CH * |t - t'| ^ α)
    {Y : (Fin 5 → ℝ) → Ω → ℝ}
    (hYc : ∀ ω, ContinuousOn (fun q => Y q ω) {q | 0 < q 3 ∧ 0 < q 4})
    (hYe : ∀ q ∈ {q : Fin 5 → ℝ | 0 < q 3 ∧ 0 < q 4},
      (fun ω => Y q ω) =ᵐ[P] fun ω => X ω (nu5 W ((n : ℝ) + 1) q))
    {a b : ℚ} (ha : (0 : ℝ) < a) (hab : (a : ℝ) ≤ b) :
    ∀ᵐ ω ∂P, ∀ st ∈ Icc (a : ℝ) b ×ˢ Icc (0 : ℝ) ((n : ℝ) + 1),
      IsRegularWith (coordChange (rescale (X ω) Q st.1) (fwdMapInv W st.2) Q)
        (witS Y W Q ω st) := by
  have hW := hWg.1
  have hW0 := hWg.2.1
  set T : ℝ := (n : ℝ) + 1 with hTdef
  have hT : 0 < T := by positivity
  set A : Set (ℝ × ℝ) := Icc (a : ℝ) b ×ˢ Icc (0 : ℝ) T with hA
  have hApos : ∀ st ∈ A, 0 < st.1 := fun st h => ha.trans_le h.1.1
  set G : Ω → ℝ × ℝ → ℂ × ℝ → ℝ := witS Y W Q with hG
  obtain ⟨D, hDc, hDA, hAD⟩ := TopologicalSpace.exists_countable_dense_subset A
  obtain ⟨D4, hD4c, hD4S, hSD4⟩ := TopologicalSpace.exists_countable_dense_subset
    (A ×ˢ ((Hbar ×ˢ Ioi (0 : ℝ)) ×ˢ Ioi (0 : ℝ)))
  have hDfc := continuousOn_Dfix hW hW0 hT.le 0 (continuous_const (y := (0 : ℝ))) Q
  have hGc : ∀ ω, ContinuousOn (fun q : (ℝ × ℝ) × (ℂ × ℝ) => G ω q.1 q.2)
      (A ×ˢ (Hbar ×ˢ Ioi 0)) := fun ω =>
    (continuousOn_witS hW hW0 hT.le Q ω (hYc ω)).mono fun q hq =>
      ⟨⟨hApos q.1 hq.1, hq.1.2⟩, hq.2⟩
  -- raw identity at countably many parameters
  have hraw : ∀ᵐ ω ∂P, ∀ st ∈ D, ∀ k : ℕ, ∀ d ∈ Dy,
      coordChange (rescale (X ω) Q st.1) (fwdMapInv W st.2) Q (foldedCircle d (radius k)) =
        G ω st (d, radius k) := by
    refine (eventually_countable_ball hDc).2 fun st hst => ae_all_iff.2 fun k =>
      (eventually_countable_ball countable_Dy).2 fun d hd => ?_
    have hst' := hDA hst
    have hs : 0 < st.1 := hApos st hst'
    have ht : st.2 ∈ Icc (0 : ℝ) T := hst'.2
    filter_upwards [ae_tendsto_rescale_νT_fixed hX hWg Q d
      (radius_pos k) ht.1 hs, hYe (q5 st.2 d st.1 (radius k)) ⟨hs, radius_pos k⟩] with ω h1 h2
    have e1 : evalReg (rescale (X ω) Q st.1) (νT W d (radius k) st.2) =
        X ω ((νT W d (radius k) st.2).map fun z => (st.1 : ℂ) * z) + Q * Real.log st.1 :=
      h1.limUnder_eq
    rw [nu5_q5 hW hW0 ht (Dy_subset_Hbar hd) st.1 (radius_pos k),
      fc_map_dmap hW hW0 ht.1 st.1 d (radius_pos k)] at h2
    rw [coordChange_rescale_fc (X ω) hW hW0 ht.1 Q st.1 d (radius_pos k), e1]
    simp only [hG, witS]
    rw [h2]
  -- commutation at countably many parameters
  have hcomm : ∀ᵐ ω ∂P, ∀ q ∈ D4, ∫ u, G ω q.1 (u, q.2.2) ∂foldedCircle q.2.1.1 q.2.1.2 =
      ∫ v, G ω q.1 (v, q.2.1.2) ∂foldedCircle q.2.1.1 q.2.2 := by
    refine (eventually_countable_ball hD4c).2 fun q hq => ?_
    obtain ⟨hqA, ⟨hc, hr⟩, hρ⟩ := hD4S hq
    have hs : 0 < q.1.1 := hApos q.1 hqA
    have ht : q.1.2 ∈ Icc (0 : ℝ) T := hqA.2
    have hV := continuous_vRev hW q.1.2
    filter_upwards [ae_comm_Y5 hX hW hW0 hYc hYe ht hs hc hr hρ] with ω h
    have iY : ∀ σ a : ℝ, 0 < σ → 0 < a →
        Integrable (fun u => Y (q5 q.1.2 u q.1.1 σ) ω) (foldedCircle q.2.1.1 a) :=
      fun σ a hσ ha => RegClosure.integrable_fc ((hYc ω).comp_continuous
        (continuous_q5_fst _ _ σ) fun _ => ⟨hs, hσ⟩).continuousOn _ ha.le
    have iD : ∀ σ a : ℝ, 0 < σ → 0 < a → Integrable
        (fun u => Dfix W 0 (fun _ => 0) Q (q.1.2, (u, σ))) (foldedCircle q.2.1.1 a) := by
      intro σ a hσ ha
      have hDc : Continuous fun u : ℂ => Dfun (vRev W q.1.2) q.1.2 0 (fun _ => 0) Q (u, σ) :=
        (continuousOn_Dfun (W := vRev W q.1.2) (T := q.1.2) hV ht.1 0 continuous_const
          Q).comp_continuous (continuous_id.prodMk continuous_const) fun _ => hσ
      exact RegClosure.integrable_fc hDc.continuousOn _ ha.le
    simp only [hG, witS]
    rw [integral_add_const_add (iY _ _ hρ hr) (iD _ _ hρ hr),
      integral_add_const_add (iY _ _ hr hρ) (iD _ _ hr hρ), h]
    congr 1
    exact integral_Dfun_swap (W := vRev W q.1.2) (T := q.1.2) hV ht.1 0 continuous_const Q _ hr hρ
  -- continuity in the parameters of the raw values at dyadic circles
  have hyc : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ d ∈ Dy, ContinuousOn (fun st : ℝ × ℝ =>
      coordChange (rescale (X ω) Q st.1) (fwdMapInv W st.2) Q (foldedCircle d (radius k))) A := by
    have hlohi : ∀ i, (((![0, a] : Fin 2 → ℚ) i : ℚ) : ℝ) ≤
        ((![(n : ℚ) + 1, b] : Fin 2 → ℚ) i : ℝ) := by
      intro i
      fin_cases i
      · simp only [Fin.zero_eta, Matrix.cons_val_zero, Rat.cast_zero]; positivity
      · simpa using hab
    refine ae_all_iff.2 fun k => (eventually_countable_ball countable_Dy).2 fun d hd => ?_
    filter_upwards [ae_continuousOn_evalReg_rescale_box hX hW hW0 hT hα hα1 hCH hH d
      (radius_pos k) Q hlohi (by simp) (by simp [hTdef]) (by simpa using ha)] with ω hω
    have hmap : MapsTo (fun st : ℝ × ℝ => (![st.2, st.1] : Fin 2 → ℝ)) A
        (ratBox ![0, a] ![(n : ℚ) + 1, b]) := by
      intro st hst i _
      fin_cases i
      · simpa [hTdef] using hst.2
      · simpa using hst.1
    have h1 := hω.comp (by fun_prop : Continuous fun st : ℝ × ℝ =>
      (![st.2, st.1] : Fin 2 → ℝ)).continuousOn hmap
    have h2 : ContinuousOn (fun st : ℝ × ℝ => Dfix W 0 (fun _ => 0) Q (st.2, (d, radius k))) A :=
      hDfc.comp (by fun_prop : Continuous fun st : ℝ × ℝ => (st.2, (d, radius k))).continuousOn
        fun st hst => ⟨hst.2, Dy_subset_Hbar hd, radius_pos k⟩
    refine (h1.add h2).congr fun st hst => ?_
    rw [coordChange_rescale_fc (X ω) hW hW0 hst.2.1 Q st.1 d (radius_pos k)]
    rfl
  filter_upwards [hraw, hcomm, hyc] with ω h1 h2 h3 st hst
  exact forall_isRegularWith_of_joint_gen (hGc ω) h3 hDA hAD h1 hD4S hSD4 h2 st hst

/-- **The scale joint witness up to time `n + 1`**, with the explicit witness `witS`. -/
theorem exists_witS [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {W : ℝ → ℝ} (hWg : DrvGood W) (Q : ℝ) (n : ℕ) :
    ∃ Y : (Fin 5 → ℝ) → Ω → ℝ,
      (∀ ω, ContinuousOn (fun q => Y q ω) {q | 0 < q 3 ∧ 0 < q 4}) ∧
      (∀ q ∈ {q : Fin 5 → ℝ | 0 < q 3 ∧ 0 < q 4},
        (fun ω => Y q ω) =ᵐ[P] fun ω => X ω (nu5 W ((n : ℝ) + 1) q)) ∧
      ∀ᵐ ω ∂P, ∀ s : ℝ, 0 < s → ∀ t ∈ Icc (0 : ℝ) ((n : ℝ) + 1),
        IsRegularWith (coordChange (rescale (X ω) Q s) (fwdMapInv W t) Q)
          (witS Y W Q ω (s, t)) := by
  have hT : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  obtain ⟨α, CH, hα, hα1, hCH, hH⟩ := hWg.2.2.1 _ hT
  obtain ⟨Y, hYc, hYe⟩ := exists_contMod_νT_rescale' hX hWg.1 hWg.2.1 hT hα hα1 hCH hH
  refine ⟨Y, hYc, hYe, ?_⟩
  have hbox : ∀ ab : ℚ × ℚ, ∀ᵐ ω ∂P, ((0 : ℝ) < ab.1 ∧ (ab.1 : ℝ) ≤ ab.2) →
      ∀ st ∈ Icc (ab.1 : ℝ) ab.2 ×ˢ Icc (0 : ℝ) ((n : ℝ) + 1),
        IsRegularWith (coordChange (rescale (X ω) Q st.1) (fwdMapInv W st.2) Q)
          (witS Y W Q ω st) := by
    intro ab
    by_cases hc : (0 : ℝ) < ab.1 ∧ (ab.1 : ℝ) ≤ ab.2
    · filter_upwards [ae_isRegularWith_rescale_box hX hWg Q n hα hα1 hCH hH hYc hYe hc.1 hc.2]
        with ω hω _
      exact hω
    · exact ae_of_all _ fun ω h => absurd h hc
  filter_upwards [ae_all_iff.2 hbox] with ω hω s hs t ht
  obtain ⟨a, ha0, has⟩ := exists_rat_btwn hs
  obtain ⟨b, hb⟩ := exists_rat_gt s
  exact hω (a, b) ⟨ha0, has.le.trans hb.le⟩ (s, t) ⟨⟨has.le, hb.le⟩, ht⟩

/-- **The scale joint witness**: almost surely, for every scale `s > 0` and time `t ≥ 0`, the
unzipped rescaled field is a regular sample. -/
theorem ae_isRegularWith_rescale_all [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {W : ℝ → ℝ} (hWg : DrvGood W) (Q : ℝ) :
    ∀ᵐ ω ∂P, ∀ s : ℝ, 0 < s → ∀ t : ℝ, 0 ≤ t → ∃ Z : ℂ × ℝ → ℝ,
      IsRegularWith (coordChange (rescale (X ω) Q s) (fwdMapInv W t) Q) Z := by
  have h : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ s : ℝ, 0 < s → ∀ t ∈ Icc (0 : ℝ) ((n : ℝ) + 1),
      ∃ Z : ℂ × ℝ → ℝ, IsRegularWith (coordChange (rescale (X ω) Q s) (fwdMapInv W t) Q) Z := by
    intro n
    obtain ⟨Y, -, -, hY⟩ := exists_witS hX hWg Q n
    filter_upwards [hY] with ω hω s hs t ht
    exact ⟨_, hω s hs t ht⟩
  filter_upwards [ae_all_iff.2 h] with ω hω s hs t ht
  obtain ⟨n, hn⟩ := exists_nat_gt t
  exact hω n s hs t ⟨ht, by linarith⟩

end ASep
end QuantumZipper
