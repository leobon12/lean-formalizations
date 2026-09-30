import QuantumZipper.Proofs.Zipper.E4LimMain

/-!
# E4 for continuous cylinder test functions (collision strictly before `T`)

`handoff/E4.md`, item E4, first step: `T₀ ↑ T` in E4-LIM (`e4_lim`). With `T₀ = T − T/(k+2)`,
`1{τ_x ≤ T₀} → 1{τ_x < T}` pointwise (`tendsto_ite_cap`), and dominated convergence
(`tendsto_iter_lintegral`, bound `1`, a.e.-measurability from `e4_lim`) gives `e4_cyl`:
E4Stmt's identity for `Ψ = cylPsi u g`, `Φ = cylPhi I f`, together with the a.e.-measurability
of both integrands (`GoodPair`), as needed by the monotone-class extension.

L3 is `tendsto_lintegral_targetField_coll` (`E4L3.lean`); the one remaining hypothesis is its
interior form `hL3i` (right-continuity of the target-field law at live times `s < T`). Own argument
(Sheffield, arXiv:1012.4797, proof of Lemma 5.6, pp. 66–68, limiting step).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E4Grid

open B2 E1 CoordsFull PalmNorm

/-- `1{h ≤ T₀_k} → 1{h < T}` for caps `T₀_k < T`, `T₀_k → T`. -/
theorem tendsto_ite_cap {T : ℝ} (hT : 0 < T) {T₀ : ℕ → ℝ} (hlt : ∀ k, T₀ k < T)
    (ht : Tendsto T₀ atTop (𝓝 T)) (h v : ℝ≥0∞) :
    Tendsto (fun k => if h ≤ ENNReal.ofReal (T₀ k) then v else 0) atTop
      (𝓝 (if h < ENNReal.ofReal T then v else 0)) := by
  by_cases hh : h < ENNReal.ofReal T
  · rw [if_pos hh]
    have hr : h = ENNReal.ofReal h.toReal := (ENNReal.ofReal_toReal (ne_top_of_lt hh)).symm
    have hrT : h.toReal < T := by
      rw [hr] at hh; exact (ENNReal.ofReal_lt_ofReal_iff hT).1 hh
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [ht.eventually (lt_mem_nhds hrT)] with k hk
    exact (if_pos (by rw [hr]; exact ENNReal.ofReal_le_ofReal hk.le)).symm
  · rw [if_neg hh]
    exact tendsto_const_nhds.congr fun k =>
      (if_neg fun hk => hh (hk.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hT).2 (hlt k)))).symm

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {ϖ : Measure ℂ}

/-- **E4 for continuous cylinder test functions**, with the a.e.-measurability of both sides,
given the interior form `hL3i` of L3. -/
theorem e4_cyl (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) (hϖ : IsNormalizer ϖ)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X' : Ω' → FieldSample} (hX' : IsFreeGFFModConstH X' P') {δ : ℝ} (hδ : 0 < δ)
    {m : ℕ} {u : Fin m → ℝ≥0} {g : ℝ × (Fin m → ℝ) × (Fin m → ℝ) → ℝ≥0∞}
    (hg : Continuous g) (hg1 : ∀ p, g p ≤ 1)
    {m' : ℕ} {I : Fin m' → ℕ} {f : (Fin m' → ℝ) → ℝ≥0∞} (hf : Continuous f) (hf1 : ∀ c, f c ≤ 1)
    (hL3i : ∀ᵐ ω ∂P, ∀ x < 0, ∀ s, 0 ≤ s → s < T → IsLive (Vr κ T B ω) s x →
      ContinuousWithinAt (fun s => ∫⁻ ω', cylPhi I f (coordsFull
          (targetField κ (Vr κ T B ω) s ϖ x (X' ω'))) ∂P') (Ici s) s) :
    ∫⁻ ω, ∫⁻ x in Icc (-δ) 0, lhsInt κ T B X ϖ
        (fun ω => {x | realHitTime (Vr κ T B ω) x < ENNReal.ofReal T}) (cylPsi u g) (cylPhi I f)
        ω x ∂nuPalm κ T B X ϖ ω ∂P =
      ∫⁻ ω, ∫⁻ x in Icc (-δ) 0, rhsInt κ T B ϖ P' X'
        (fun ω => {x | realHitTime (Vr κ T B ω) x < ENNReal.ofReal T}) (cylPsi u g) (cylPhi I f)
        ω x ∂nuPalm κ T B X ϖ ω ∂P ∧
    GoodPair P (fun ω => nuPalm κ T B X ϖ ω) (Icc (-δ) 0) (lhsInt κ T B X ϖ
        (fun ω => {x | realHitTime (Vr κ T B ω) x < ENNReal.ofReal T}) (cylPsi u g) (cylPhi I f))
      (rhsInt κ T B ϖ P' X'
        (fun ω => {x | realHitTime (Vr κ T B ω) x < ENNReal.ofReal T}) (cylPsi u g)
        (cylPhi I f)) := by
  have hL3 : ∀ᵐ ω ∂P, ∀ x < 0, ∀ τ, realHitTime (Vr κ T B ω) x = ENNReal.ofReal τ → τ < T →
      Tendsto (fun s => ∫⁻ ω', cylPhi I f (coordsFull
          (targetField κ (Vr κ T B ω) s ϖ x (X' ω'))) ∂P') (𝓝[<] τ)
        (𝓝 (∫⁻ ω', cylPhi I f (coordsFull (targetColl κ (Vr κ T B ω) τ ϖ (X' ω'))) ∂P')) := by
    filter_upwards [hB.cont] with ω hc x hx τ hτ _
    exact tendsto_lintegral_targetField_coll κ (continuous_vrev (drive_continuous hc) T)
      (vrev_zero hT.le) hx.ne hτ hϖ hX' I hf hf1
  set T₀ : ℕ → ℝ := fun k => T - T / ((k + 2 : ℕ) : ℝ) with hT₀def
  have hpos : ∀ k : ℕ, (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := fun k => Nat.cast_pos.2 (by omega)
  have hT₀lt : ∀ k, T₀ k < T := fun k => by
    have := div_pos hT (hpos k)
    simp only [hT₀def]; linarith
  have hT₀pos : ∀ k, 0 < T₀ k := fun k => by
    have : T / ((k + 2 : ℕ) : ℝ) < T := div_lt_self hT (by
      have : (2 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by push_cast; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
      linarith)
    simp only [hT₀def]; linarith
  have hT₀t : Tendsto T₀ atTop (𝓝 T) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat T).comp (tendsto_add_atTop_nat 2)
    simpa [hT₀def, Function.comp_def] using (tendsto_const_nhds (x := T)).sub h
  have hk := fun k => e4_lim hκ hκ4 hT hB hX hind hϖ hX' (hT₀pos k) (hT₀lt k) hδ (u := u) hg hg1 hf hf1
    (by
      filter_upwards [hL3] with ω h x hx τ hτ hτT
      exact h x hx τ hτ (hτT.trans_lt (hT₀lt k)))
    (by
      filter_upwards [hL3i] with ω h x hx s hs0 hsT hl
      exact h x hx s hs0 (hsT.trans (hT₀lt k)) hl)
  have hfin : ∀ ω, nuPalm κ T B X ϖ ω (Icc (-δ) 0) < ⊤ := fun ω =>
    qBoundaryMeasure_Icc_lt_top _ _ _ _
  have hint := (EWire.zfin hκ hκ4 hT hδ hB hX hind hϖ (ϖ := ϖ)).2.2.ne
  have hL := tendsto_iter_lintegral (P := P) hfin hint
    (a := fun k => lhsInt κ T B X ϖ
      (fun ω => {x | realHitTime (Vr κ T B ω) x ≤ ENNReal.ofReal (T₀ k)}) (cylPsi u g)
        (cylPhi I f))
    (b := lhsInt κ T B X ϖ
      (fun ω => {x | realHitTime (Vr κ T B ω) x < ENNReal.ofReal T}) (cylPsi u g) (cylPhi I f))
    (fun k ω x => indicator_apply_le' (fun _ => mul_le_one' (hg1 _) (hf1 _)) fun _ => zero_le)
    (ae_all_iff.2 fun k => (hk k).2.2.1) (fun k => (hk k).2.1)
    (Eventually.of_forall fun ω => Eventually.of_forall fun x => by
      simp only [lhsInt, indicator_apply, mem_setOf_eq]
      exact tendsto_ite_cap hT hT₀lt hT₀t _ _)
  have hR := tendsto_iter_lintegral (P := P) hfin hint
    (a := fun k => rhsInt κ T B ϖ P' X'
      (fun ω => {x | realHitTime (Vr κ T B ω) x ≤ ENNReal.ofReal (T₀ k)}) (cylPsi u g)
        (cylPhi I f))
    (b := rhsInt κ T B ϖ P' X'
      (fun ω => {x | realHitTime (Vr κ T B ω) x < ENNReal.ofReal T}) (cylPsi u g) (cylPhi I f))
    (fun k ω x => indicator_apply_le' (fun _ => mul_le_one' (hg1 _)
      (lintegral_le_one_of_le_one fun _ => hf1 _)) fun _ => zero_le)
    (ae_all_iff.2 fun k => (hk k).2.2.2.2) (fun k => (hk k).2.2.2.1)
    (Eventually.of_forall fun ω => Eventually.of_forall fun x => by
      simp only [rhsInt, indicator_apply, mem_setOf_eq]
      exact tendsto_ite_cap hT hT₀lt hT₀t _ _)
  exact ⟨tendsto_nhds_unique hL.1 (hR.1.congr fun k => ((hk k).1).symm),
    hL.2.1, hL.2.2, hR.2.1, hR.2.2⟩

end E4Grid
end QuantumZipper
