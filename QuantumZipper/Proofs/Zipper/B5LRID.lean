import QuantumZipper.Proofs.Zipper.B5ZeroMinus
import QuantumZipper.Proofs.Zipper.ESMLRID
import QuantumZipper.Proofs.Zipper.E1NuExist
import QuantumZipper.Proofs.Zipper.B2Driver

/-!
# LR-ID at the sample level, corrected form (conditional on B5-V)

Node **LR-ID** (E-SM-inst (a)) of `handoff/E-PLAN-2.md`, in the corrected form of
`handoff/ESM.md`: the `ℓ`-indicator carries `tLen ℓ < T` (without it the E-PLAN-2 statement is
false: for `ℓ > L⁻_T` the point `zeroMinus V (T − tLen ℓ)` is evaluated at a negative time).

* `lenTime_mem_Ioo_iff` (deterministic): for `ℓ > 0`, `0 < tᴸ ℓ < T ↔ ℓ < ν[a, 0]`.
* `lintegral_collided_eq` (deterministic): the Palm integral over collided points in `[−δ, 0]`
  equals the length integral with the corrected indicator.
* `ae_nu0_regular`: under B3(a), a.s. `ν_{h⁰}` is atomless, positive on intervals, locally finite.
* **`ae_lr_id`**: LR-ID, a.s., from B3(a), `RohdeSchrammSimple` and **B5-V** (hypothesis `hB5V`;
  B5-V itself is not proved here, see the report / `handoff/B5.md`).

Sources: Sheffield, arXiv:1012.4797, Lemma 5.6 and its proof (pp. 66–68); the change of variables
is `ESM.lintegral_Ioc_eq_lintegral_lenTime` (own elementary argument, as documented there).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace B5

section Det

variable {ν : Measure ℝ} {a T : ℝ} {z τ : ℝ → ℝ} {A : ℝ → ℝ≥0∞}

/-- For `ℓ > 0`: `0 < tᴸ ℓ < T` iff `ℓ < ν[a, 0]`. -/
lemma lenTime_mem_Ioo_iff (hatom : ∀ x, ν {x} = 0) (hpos : ∀ u v, u < v → 0 < ν (Ioo u v))
    (ha : a < 0) (hfin : ν (Icc a 0) < ⊤) (hT : 0 < T)
    (hA : ∀ s ∈ Icc 0 T, A s = ν (Icc a (z (T - s))))
    (hz : StrictAntiOn z (Icc 0 T)) (hzT : z T = a) (hz0 : z 0 = 0)
    (hτ : ∀ x ∈ Ioc a 0, τ x ∈ Icc 0 T ∧ z (τ x) = x) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (0 < ESM.lenTime A ℓ ∧ ESM.lenTime A ℓ < T) ↔ ℓ < (ν (Icc a 0)).toReal := by
  constructor
  · rintro ⟨h1, h2⟩
    by_contra hge
    push Not at hge
    have hS : ∀ s, 0 ≤ s → ENNReal.ofReal ℓ ≤ A s → T ≤ s := by
      intro s hs hle
      by_contra hsT
      push Not at hsT
      have hmem : T - s ∈ Icc 0 T := ⟨by linarith, by linarith⟩
      have hzlt : z (T - s) < 0 := hz0 ▸ hz ⟨le_rfl, hT.le⟩ hmem (by linarith)
      have haz : a ≤ z (T - s) := by
        rcases eq_or_lt_of_le hmem.2 with h | h
        · rw [h, hzT]
        · exact hzT ▸ (hz hmem ⟨hT.le, le_rfl⟩ h).le
      have hlt := ESM.lrcv_measure_lt hpos haz hzlt
        (ne_top_of_le_ne_top hfin.ne (measure_mono (Icc_subset_Icc_right hzlt.le)))
      rw [← hA s ⟨hs, hsT.le⟩] at hlt
      have h3 : ENNReal.ofReal ℓ < ENNReal.ofReal (ν (Icc a 0)).toReal := by
        rw [ENNReal.ofReal_toReal hfin.ne]; exact lt_of_le_of_lt hle hlt
      exact absurd ((ENNReal.ofReal_lt_ofReal_iff'.1 h3).1) (not_lt.2 hge)
    unfold ESM.lenTime at h1 h2
    by_cases hne : {s | 0 ≤ s ∧ ENNReal.ofReal ℓ ≤ A s}.Nonempty
    · have := le_csInf hne (fun s hs => hS s hs.1 hs.2)
      linarith
    · rw [not_nonempty_iff_eq_empty.1 hne, Real.sInf_empty] at h1
      exact lt_irrefl _ h1
  · intro hlt
    obtain ⟨x, hx, hFx⟩ : ∃ x ∈ Icc a 0, ESM.lenFn ν a 0 x = ℓ := by
      have := intermediate_value_Icc ha.le (ESM.continuous_lenFn hatom hfin).continuousOn
      rw [ESM.lenFn_left ha.le hatom, ESM.lenFn_of_ge (le_refl (0 : ℝ))] at this
      exact this ⟨hℓ.le, hlt.le⟩
    have hxa : x ≠ a := by
      rintro rfl; rw [ESM.lenFn_left ha.le hatom] at hFx; linarith
    have hx0 : x ≠ 0 := by
      rintro rfl; rw [ESM.lenFn_of_ge (le_refl (0 : ℝ))] at hFx; linarith
    have hxI : x ∈ Ioc a 0 := ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), hx.2⟩
    obtain ⟨hτI, hzτ⟩ := hτ x hxI
    rw [← hFx, ESM.lenTime_lenFn hpos hfin hT.le hA hz hzT hxI hτI hzτ]
    constructor
    · have : τ x ≠ T := by rintro h; rw [h, hzT] at hzτ; exact hxa hzτ.symm
      linarith [lt_of_le_of_ne hτI.2 this]
    · have : τ x ≠ 0 := by rintro h; rw [h, hz0] at hzτ; exact hx0 hzτ.symm
      linarith [lt_of_le_of_ne hτI.1 (Ne.symm this)]

/-- **LR-ID, deterministic form (corrected indicator).** With `S` the set of points colliding
strictly before `T` (`x ∈ S ↔ a < x` for `x ≤ 0`), for every `F ≥ 0`:
`∫⁻_{[−δ,0]} 1_S(x) F(x, T − τ x) dν = ∫⁻_{ℓ>0} 1{0 < tᴸ ℓ < T, −δ ≤ z(T − tᴸ ℓ)}
  F(z(T − tᴸ ℓ), tᴸ ℓ) dℓ`. -/
theorem lintegral_collided_eq (hatom : ∀ x, ν {x} = 0) (hpos : ∀ u v, u < v → 0 < ν (Ioo u v))
    (ha : a < 0) (hfin : ν (Icc a 0) < ⊤) (hT : 0 < T)
    (hA : ∀ s ∈ Icc 0 T, A s = ν (Icc a (z (T - s))))
    (hz : StrictAntiOn z (Icc 0 T)) (hzT : z T = a) (hz0 : z 0 = 0)
    (hτ : ∀ x ∈ Ioc a 0, τ x ∈ Icc 0 T ∧ z (τ x) = x) {S : Set ℝ}
    (hS : ∀ x ≤ 0, x ∈ S ↔ a < x) (δ : ℝ) (F : ℝ → ℝ → ℝ≥0∞) :
    ∫⁻ x in Icc (-δ) 0, S.indicator (fun x => F x (T - τ x)) x ∂ν =
      ∫⁻ ℓ in Ioi 0, {ℓ | 0 < ESM.lenTime A ℓ ∧ ESM.lenTime A ℓ < T ∧
          -δ ≤ z (T - ESM.lenTime A ℓ)}.indicator
        (fun ℓ => F (z (T - ESM.lenTime A ℓ)) (ESM.lenTime A ℓ)) ℓ := by
  set Φ : ℝ → ℝ → ℝ≥0∞ := fun x s => (Icc (-δ) 0).indicator (fun x => F x s) x with hΦ
  have hL : ∫⁻ x in Icc (-δ) 0, S.indicator (fun x => F x (T - τ x)) x ∂ν =
      ∫⁻ x in Ioc a 0, Φ x (T - τ x) ∂ν := by
    rw [← lintegral_indicator measurableSet_Icc, ← lintegral_indicator measurableSet_Ioc]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ Icc (-δ) 0
    · rw [indicator_of_mem hx]
      by_cases hax : a < x
      · rw [indicator_of_mem ((hS x hx.2).2 hax), indicator_of_mem (show x ∈ Ioc a 0 from ⟨hax, hx.2⟩), hΦ]
        simp only
        rw [indicator_of_mem hx]
      · rw [indicator_of_notMem (fun h => hax ((hS x hx.2).1 h)),
          indicator_of_notMem (fun h : x ∈ Ioc a 0 => hax h.1)]
    · rw [indicator_of_notMem hx]
      by_cases hx' : x ∈ Ioc a 0
      · rw [indicator_of_mem hx', hΦ]
        simp only
        rw [indicator_of_notMem hx]
      · rw [indicator_of_notMem hx']
  rw [hL, ESM.lintegral_Ioc_eq_lintegral_lenTime hatom hpos ha.le hfin hT.le hA hz hzT hτ Φ]
  set L := (ν (Icc a 0)).toReal
  have hR : EqOn (fun ℓ => {ℓ | 0 < ESM.lenTime A ℓ ∧ ESM.lenTime A ℓ < T ∧
          -δ ≤ z (T - ESM.lenTime A ℓ)}.indicator
        (fun ℓ => F (z (T - ESM.lenTime A ℓ)) (ESM.lenTime A ℓ)) ℓ)
      ((Ioo 0 L).indicator fun ℓ => Φ (z (T - ESM.lenTime A ℓ)) (ESM.lenTime A ℓ)) (Ioi 0) := by
    intro ℓ hℓ
    have hiff := lenTime_mem_Ioo_iff hatom hpos ha hfin hT hA hz hzT hz0 hτ (ℓ := ℓ) hℓ
    simp only
    by_cases hlt : ℓ < L
    · obtain ⟨h1, h2⟩ := hiff.2 hlt
      have hmem : T - ESM.lenTime A ℓ ∈ Icc 0 T := ⟨by linarith, by linarith⟩
      have hzneg : z (T - ESM.lenTime A ℓ) ≤ 0 :=
        (hz0 ▸ hz ⟨le_rfl, hT.le⟩ hmem (by linarith)).le
      rw [indicator_of_mem (show ℓ ∈ Ioo 0 L from ⟨hℓ, hlt⟩), hΦ]
      simp only
      by_cases hd : -δ ≤ z (T - ESM.lenTime A ℓ)
      · rw [indicator_of_mem (show ℓ ∈ {ℓ | 0 < ESM.lenTime A ℓ ∧ ESM.lenTime A ℓ < T ∧
          -δ ≤ z (T - ESM.lenTime A ℓ)} from ⟨h1, h2, hd⟩), indicator_of_mem (show z (T - ESM.lenTime A ℓ) ∈ Icc (-δ) 0 from ⟨hd, hzneg⟩)]
      · rw [indicator_of_notMem (fun h : ℓ ∈ {ℓ | 0 < ESM.lenTime A ℓ ∧ ESM.lenTime A ℓ < T ∧
          -δ ≤ z (T - ESM.lenTime A ℓ)} => hd h.2.2),
          indicator_of_notMem (fun h : z (T - ESM.lenTime A ℓ) ∈ Icc (-δ) 0 => hd h.1)]
    · rw [indicator_of_notMem (fun h : ℓ ∈ {ℓ | 0 < ESM.lenTime A ℓ ∧ ESM.lenTime A ℓ < T ∧
          -δ ≤ z (T - ESM.lenTime A ℓ)} => hlt (hiff.1 ⟨h.1, h.2.1⟩)),
        indicator_of_notMem (fun h : ℓ ∈ Ioo 0 L => hlt h.2)]
  rw [setLIntegral_congr_fun measurableSet_Ioi hR, lintegral_indicator measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo,
    Set.inter_eq_left.2 (Ioo_subset_Ioi_self : Ioo (0 : ℝ) L ⊆ Ioi 0),
    Measure.restrict_congr_set Ioo_ae_eq_Ico]

/-- **The right side of B5-V as a length process on `[0,T]`.** `A s = ν[a, z(T − s)]` starts at
`0`, is strictly increasing and continuous on `[0,T]` (these are the properties `hAc`, `hAmono`
of E-SM, on `[0,T]`, for the right side of B5-V). -/
lemma lengthRHS_props (hatom : ∀ x, ν {x} = 0) (hpos : ∀ u v, u < v → 0 < ν (Ioo u v))
    (hfin : ν (Icc a 0) < ⊤) (hT : 0 < T) (hz : StrictAntiOn z (Icc 0 T))
    (hzc : ContinuousOn z (Icc 0 T)) (hzT : z T = a) (hz0 : z 0 = 0) :
    ν (Icc a (z (T - 0))) = 0 ∧
      StrictMonoOn (fun s => ν (Icc a (z (T - s)))) (Icc 0 T) ∧
      ContinuousOn (fun s => ν (Icc a (z (T - s)))) (Icc 0 T) := by
  have hmem : ∀ s ∈ Icc 0 T, T - s ∈ Icc 0 T := fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hge : ∀ s ∈ Icc 0 T, a ≤ z (T - s) := fun s hs => by
    rcases eq_or_lt_of_le (hmem s hs).2 with h | h
    · rw [h, hzT]
    · exact hzT ▸ (hz (hmem s hs) ⟨hT.le, le_rfl⟩ h).le
  have hle : ∀ s ∈ Icc 0 T, z (T - s) ≤ 0 := fun s hs => by
    rcases eq_or_lt_of_le (hmem s hs).1 with h | h
    · rw [← h, hz0]
    · exact hz0 ▸ (hz ⟨le_rfl, hT.le⟩ (hmem s hs) h).le
  have hfin' : ∀ s ∈ Icc 0 T, ν (Icc a (z (T - s))) ≠ ⊤ := fun s hs =>
    ne_top_of_le_ne_top hfin.ne (measure_mono (Icc_subset_Icc_right (hle s hs)))
  refine ⟨by rw [sub_zero, hzT, Icc_self, hatom], ?_, ?_⟩
  · intro s₁ hs₁ s₂ hs₂ hlt
    exact ESM.lrcv_measure_lt hpos (hge s₁ hs₁)
      (hz (hmem s₂ hs₂) (hmem s₁ hs₁) (by linarith)) (hfin' s₁ hs₁)
  · have hc : ContinuousOn (fun s => ENNReal.ofReal (ESM.lenFn ν a 0 (z (T - s)))) (Icc 0 T) :=
      ENNReal.continuous_ofReal.comp_continuousOn ((ESM.continuous_lenFn hatom hfin).comp_continuousOn
        (hzc.comp (continuousOn_const.sub continuousOn_id) hmem))
    refine hc.congr fun s hs => ?_
    simp only
    rw [ESM.lenFn_of_le (hle s hs), ENNReal.ofReal_toReal (hfin' s hs)]

end Det

/-! ## The sample-level statement -/

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- Under B3(a), a.s. `ν₀ = ν_{h⁰}` is atomless, positive on open intervals and finite on compact
intervals (transfer of `RevCouplingBoundaryMeasureRegular` by B2(a), B2(c)). -/
theorem ae_nu0_regular (hReg : Blueprint.RevCouplingBoundaryMeasureRegular) (hκ : 0 < κ)
    (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) :
    ∀ᵐ ω ∂P, (∀ x, qBoundaryMeasure (Real.sqrt κ) (B2.h0f κ T B X ω) {x} = 0) ∧
      (∀ u v : ℝ, u < v → 0 < qBoundaryMeasure (Real.sqrt κ) (B2.h0f κ T B X ω) (Ioo u v)) ∧
      (∀ u v : ℝ, qBoundaryMeasure (Real.sqrt κ) (B2.h0f κ T B X ω) (Icc u v) < ⊤) := by
  obtain ⟨B'', hB'', hind'', hV⟩ := B2.b2_V_brownian (κ := κ) hB hind hT.le
  filter_upwards [hReg κ hκ hκ4 T hT P B'' X hB'' hX hind'', hV,
    B2.b2_ident_qBoundaryMeasure hB hX hind hT.le] with ω hRω hVω hid
  have hrevV : revMap (B2.Vr κ T B ω) T = revMap (drive κ B'' ω) T :=
    funext fun z => ReverseFlow.revMap_congr_drive z hVω
  have hcf : couplingFieldRev κ (B2.Vr κ T B ω) T (X ω) =
      couplingFieldRev κ (drive κ B'' ω) T (X ω) := by
    simp only [couplingFieldRev, hrevV]
  rw [hid, hcf]
  exact hRω

/-- A.s. the right side `s ↦ ν_{h⁰}[0₋(T), 0₋(T − s)]` of B5-V vanishes at `0`, is strictly
increasing and continuous on `[0,T]`. -/
theorem ae_lengthRHS_props (hReg : Blueprint.RevCouplingBoundaryMeasureRegular)
    (hRSS : Blueprint.RohdeSchrammSimple) (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    ∀ᵐ ω ∂P,
      qBoundaryMeasure (Real.sqrt κ) (B2.h0f κ T B X ω)
          (Icc (zeroMinus (B2.Vr κ T B ω) T) (zeroMinus (B2.Vr κ T B ω) (T - 0))) = 0 ∧
      StrictMonoOn (fun s => qBoundaryMeasure (Real.sqrt κ) (B2.h0f κ T B X ω)
          (Icc (zeroMinus (B2.Vr κ T B ω) T) (zeroMinus (B2.Vr κ T B ω) (T - s)))) (Icc 0 T) ∧
      ContinuousOn (fun s => qBoundaryMeasure (Real.sqrt κ) (B2.h0f κ T B X ω)
          (Icc (zeroMinus (B2.Vr κ T B ω) T) (zeroMinus (B2.Vr κ T B ω) (T - s)))) (Icc 0 T) := by
  filter_upwards [ae_nu0_regular hReg hκ hκ4 hT hB hX hind,
    ae_zeroMinus_Vr_facts hRSS hκ hκ4.le hT P B hB] with ω hν hzf
  obtain ⟨hatom, hpos, hfin⟩ := hν
  obtain ⟨hz0, -, hanti, hzc, -, -⟩ := hzf
  exact lengthRHS_props hatom hpos (hfin _ _) hT hanti hzc rfl hz0

/-- The right side of B5-V as a length process: `ν_{h⁰}[0₋(T), 0₋(T − s)]` (meaningful for
`s ∈ [0,T]`). -/
def lenRHS (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ω : Ω) (s : ℝ) : ℝ≥0∞ :=
  qBoundaryMeasure (Real.sqrt κ) (B2.h0f κ T B X ω)
    (Icc (zeroMinus (B2.Vr κ T B ω) T) (zeroMinus (B2.Vr κ T B ω) (T - s)))

/-- **LR-ID with the length process `lenRHS`, unconditional** (no B5-V): the same identity as
`ae_lr_id`, with `tᴸ` the level times of `lenRHS` instead of those of `L⁻ = unzipLengths`. Under
B5-V the two level-time functions agree on `ℓ > 0` with `0 < tᴸ ℓ < T` (`ae_lr_id`). -/
theorem ae_lr_id_rhs (hReg : Blueprint.RevCouplingBoundaryMeasureRegular)
    (hRSS : Blueprint.RohdeSchrammSimple) (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (ϖ : Measure ℂ) (δ : ℝ) (G : Ω → ℝ → FieldSample × (ℝ → ℝ) → ℝ≥0∞) :
    ∀ᵐ ω ∂P,
      ∫⁻ x in Icc (-δ) 0, {x | realHitTime (B2.Vr κ T B ω) x < ENNReal.ofReal T}.indicator
          (fun x => G ω x (B2.collided κ T B X ω x)) x ∂E1.nuPalm κ T B X ϖ ω =
        ENNReal.ofReal (Real.exp (Real.sqrt κ * -(E1.mReg κ T B X ϖ ω) / 2)) *
          ∫⁻ ℓ in Ioi (0 : ℝ),
            {ℓ | 0 < ESM.lenTime (lenRHS κ T B X ω) ℓ ∧ ESM.lenTime (lenRHS κ T B X ω) ℓ < T ∧
                -δ ≤ zeroMinus (B2.Vr κ T B ω) (T - ESM.lenTime (lenRHS κ T B X ω) ℓ)}.indicator
              (fun ℓ => G ω (zeroMinus (B2.Vr κ T B ω) (T - ESM.lenTime (lenRHS κ T B X ω) ℓ))
                (zipCapDown (Real.sqrt κ) (ESM.lenTime (lenRHS κ T B X ω) ℓ)
                  (B2.cfg κ B X ω))) ℓ := by
  filter_upwards [ae_nu0_regular hReg hκ hκ4 hT hB hX hind,
    ae_zeroMinus_Vr_facts hRSS hκ hκ4.le hT P B hB,
    E1.ae_nuPalm_eq_smul (κ := κ) hB hX hind hT.le ϖ] with ω hν hzf hpalm
  obtain ⟨hatom, hpos, hfin⟩ := hν
  obtain ⟨hz0, ha, hanti, -, hhit, hiff⟩ := hzf
  rw [hpalm, Measure.restrict_smul, lintegral_smul_measure]
  congr 1
  exact lintegral_collided_eq (τ := fun x => (realHitTime (B2.Vr κ T B ω) x).toReal)
    (A := lenRHS κ T B X ω) hatom hpos ha (hfin _ _) hT (fun s _ => rfl) hanti rfl hz0
    (fun x hx => ⟨(hhit x hx).2.1, (hhit x hx).2.2⟩)
    (S := {x | realHitTime (B2.Vr κ T B ω) x < ENNReal.ofReal T}) (fun x hx => hiff x hx) δ
    (fun x s => G ω x (zipCapDown (Real.sqrt κ) s (B2.cfg κ B X ω)))

end B5
end QuantumZipper
