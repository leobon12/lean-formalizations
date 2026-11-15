/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedS7Word
import InteractingSLE.Spec.Sec5.KillArcStage
import InteractingSLE.Foundations.Loewner.YuanCorollary13Finite

/-!
# Proposition 5.9 at depth `ℓ`, step S7 (b): the killing at the far marks after the last switch

Packet PROVE-STAGED-S7 (`planning/handoffs/PROVE-STAGED-S6.md` §5, item 1). Deterministic part of the killing of the
restarted word at its far marks: if the full staged image arc (`gCurve`) has a finite terminal capacity `T` and its
killed trace converges at `T` to a real point `x₀` beyond the left junction (or beyond the right junction), then

* the restarted driver and all restarted marks have left limits at the restarted lifetime `T − S₀`: they are, before
  `T − S₀`, the real Loewner images under the shifted **closed driver** `U` of PROVE-KILLARC
  (`KillArc.exists_closed_driver_ne`), which are continuous in time (`s3W_eq_shiftDrv`, `s6VL_eq_rightImg`,
  `s6VR_eq_rightImg`);
* the far mark (the flowed junction) meets the driver there: the junction is swallowed at `T`
  (`KillArc.killedArc_swallow`) and the restarted far mark is the flowed junction (`StagedS3.relL_shift`);
  **`isKilledAtFarLim_s6`**;
* the restarted driver has a generating trace up to `T − S₀`: the shifted Loewner tips of `U`
  (`IsLoewnerTraceLT.isLoewnerTraceLT_shift`, [Yua22] Corollary 1.3 before a horizon) are `f_{S₀}` of the future of
  the closed trace, hence converge to `f_{S₀}(x₀)` (`tendsto_shiftTip`, `isGeneratingTrace_of_isLoewnerTraceLT`);
  **`exists_isGeneratingTrace_s3W`**.

Conditional helpers with distinct names; they replace no source theorem. R48: deterministic Loewner theory only.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)

namespace InteractingSLE.Sec5.CrossCond.StagedS7

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord WangWu.SeedTail LawUnique GlueCond Word49 StagedS3 StagedS4 StagedS5 StagedS6 MartChar.RealFlow
open Prop59Pieces
open StagedFinal (imgStageVL imgStageVR rootVL rootVR)
open Prop59NodeTree (shiftDrv continuous_shiftDrv)
open QuantumZipper.RS (shiftDrive)
open Sec7.Lemma71C (capClock)

/-! ### Analytic helpers -/

section Helpers

/-- A path on `ℝ≥0` that agrees before `T'` with a function continuous on `[0, ∞)` has that function's value as its
left limit at `T'`. -/
theorem tendsto_nhdsLT_of_eq {g : ℝ≥0 → ℝ} {f : ℝ → ℝ} {T' : ℝ≥0} (hf : ContinuousOn f (Ici 0))
    (hg : ∀ r : ℝ≥0, r < T' → g r = f r) : Tendsto g (𝓝[<] T') (𝓝 (f T')) := by
  have hc : Continuous fun r : ℝ≥0 => f r :=
    continuousOn_univ.1 (hf.comp NNReal.continuous_coe.continuousOn fun r _ => r.2)
  refine ((hc.tendsto T').mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (hg r hr).symm

/-- **A generating trace from a Loewner trace before a horizon with a left limit there**: the trace frozen at its
left limit from `T` on generates every driver that agrees with `V` before `T`. -/
theorem isGeneratingTrace_of_isLoewnerTraceLT {w : ℝ≥0 → ℝ} {V : ℝ → ℝ} {T : ℝ≥0} (hT : 0 < T) {γ : ℝ → ℂ}
    (hγ : IsLoewnerTraceLT V T γ) (hwV : ∀ r : ℝ, 0 ≤ r → r < T → w r.toNNReal = V r) {L : ℂ}
    (hL : Tendsto γ (𝓝[<] (T : ℝ)) (𝓝 L)) :
    IsGeneratingTrace w T (fun r : ℝ≥0 => if r < T then γ r else L) := by
  classical
  set η : ℝ≥0 → ℂ := fun r => if r < T then γ r else L with hηdef
  have hηγ : ∀ r : ℝ≥0, r < T → η r = γ r := fun r hr => by simp only [hηdef, hr, ↓reduceIte]
  have hγc : ContinuousOn (fun r : ℝ≥0 => γ r) {r | r < T} :=
    hγ.2.1.comp NNReal.continuous_coe.continuousOn fun r hr => ⟨r.2, by exact_mod_cast hr⟩
  refine ⟨?_, fun u hu => ?_, fun t ht => ?_⟩
  · rw [hηγ 0 hT]
    simpa using hγ.1
  · have hu' : u ≤ T := by exact_mod_cast hu
    have hset : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (T : ℝ≥0∞)} = Iic T := by
      ext t
      simp only [mem_ofPred_eq, mem_Iic, ENNReal.coe_le_coe]
    rw [hset]
    rcases hu'.lt_or_eq with hlt | rfl
    · have hev : η =ᶠ[𝓝 u] fun r : ℝ≥0 => γ r := by
        filter_upwards [Iio_mem_nhds hlt] with t ht
        exact hηγ t ht
      exact ((hγc.continuousAt (Iio_mem_nhds hlt)).congr_of_eventuallyEq hev).continuousWithinAt
    · rw [← continuousWithinAt_Iio_iff_Iic]
      have hηu : η u = L := by simp only [hηdef, lt_irrefl, ↓reduceIte]
      show Tendsto η (𝓝[<] u) (𝓝 (η u))
      rw [hηu]
      have hto : Tendsto (fun r : ℝ≥0 => (r : ℝ)) (𝓝[<] u) (𝓝[<] (u : ℝ)) :=
        tendsto_nhdsWithin_iff.2 ⟨(NNReal.continuous_coe.tendsto u).mono_left nhdsWithin_le_nhds,
          eventually_nhdsWithin_of_forall fun r hr => (show (r : ℝ) < u by exact_mod_cast hr)⟩
      refine (hL.comp hto).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact (hηγ r hr).symm
  · have ht' : t < T := by exact_mod_cast ht
    obtain ⟨t₂, htt₂, ht₂T⟩ := exists_between (show (t : ℝ) < T by exact_mod_cast ht')
    have hK : fwdHull (fun s : ℝ => w s.toNNReal) t = fwdHull V t :=
      fwdHull_eq_of_eqOn t.2 htt₂ fun r hr => hwV r hr.1 (lt_of_le_of_lt hr.2 ht₂T)
    have himg : η '' Icc 0 t = γ '' Icc 0 (t : ℝ) := by
      ext z
      constructor
      · rintro ⟨r, hr, rfl⟩
        exact ⟨r, ⟨r.2, by exact_mod_cast hr.2⟩, (hηγ r (lt_of_le_of_lt hr.2 ht')).symm⟩
      · rintro ⟨r, hr, rfl⟩
        have hrt : r.toNNReal ≤ t := by rw [Real.toNNReal_le_iff_le_coe]; exact hr.2
        refine ⟨r.toNNReal, ⟨zero_le, hrt⟩, ?_⟩
        rw [hηγ _ (lt_of_le_of_lt hrt ht'), Real.coe_toNNReal _ hr.1]
    have hfill := hγ.2.2 t t.2 (by exact_mod_cast ht')
    have hA : IsCompact (γ '' Icc 0 (t : ℝ)) := hγ.isCompact_image (by exact_mod_cast ht')
    rw [hK, himg]
    exact (fillH_eq_iff_isFilling_of_isClosed hA.isBounded hA.isClosed ((QuantumZipper.fwdHull_mono).2 _)).2 hfill

/-- **The shifted Loewner tips converge at the horizon** when the trace before the horizon is a simple arc in `ℍ`
ending at a real point `x₀` with a forward solution up to `S₀`: `γ_{S₀}(u) = f_{S₀}(η(S₀ + u))` for
`0 < u < T − S₀` and `f_{S₀}` is continuous at `x₀` from `ℍ`. -/
theorem tendsto_shiftTip {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {T S₀ : ℝ} (hS₀ : 0 ≤ S₀)
    (hS₀T : S₀ < T) {η : ℝ → ℂ} (hLT : IsLoewnerTraceLT U T η) (hc : ContinuousOn η (Icc 0 T))
    (hinj : InjOn η (Icc 0 T)) (hH : MapsTo η (Ioo 0 T) H) {x₀ : ℝ} (hx₀ : η T = x₀) {v : ℝ → ℂ}
    (hv : QuantumZipper.IsForwardSol U x₀ S₀ v) :
    Tendsto (loewnerTip (shiftDrive U S₀)) (𝓝[<] (T - S₀)) (𝓝 (v S₀)) := by
  obtain ⟨hLTs, hext⟩ := hLT.isLoewnerTraceLT_shift hU hU0 hS₀
  set γa := loewnerTip (shiftDrive U S₀) with hγadef
  have hTS : 0 < T - S₀ := sub_pos.2 hS₀T
  have hK : fwdHull U S₀ = η '' Ioc 0 S₀ := by
    rw [hLT.2.2 S₀ hS₀ hS₀T]
    exact YuanCharacterisation.fillH_image_eq hS₀ (hc.mono (Icc_subset_Icc_right hS₀T.le))
      (hinj.mono (Icc_subset_Icc_right hS₀T.le)) (by rw [hLT.1]; simp)
      (fun u hu => hH ⟨hu.1, lt_of_le_of_lt hu.2 hS₀T⟩)
  have hkey : ∀ u, 0 < u → u < T - S₀ → γa u = fwdMap U S₀ (η (S₀ + u)) := by
    intro u hu0 huT
    have hSu : S₀ + u ∈ Ioo 0 T := ⟨by linarith, by linarith⟩
    have hηH : η (S₀ + u) ∈ H := hH hSu
    have hηK : η (S₀ + u) ∉ fwdHull U S₀ := by
      rw [hK]
      rintro ⟨r, hr, he⟩
      have := hinj ⟨hr.1.le, hr.2.trans hS₀T.le⟩ ⟨hSu.1.le, hSu.2.le⟩ he
      linarith [hr.2]
    have hF := hext u hu0.le huT
    have hγHb : γa u ∈ Hbar := Sec7.IsLoewnerTraceLT.mem_Hbar hLTs (QuantumZipper.RS.continuous_shiftDrive hU S₀)
      (StagedFinal.shiftDrive_zero_apply U S₀) hu0.le huT
    have hγH : γa u ∈ H := by
      rcases (show 0 ≤ (γa u).im from hγHb).lt_or_eq with h | h
      · exact h
      · have hmem : extendFrom H (fwdMapInv U S₀) (γa u) ∈ H \ fwdHull U S₀ := by
          rw [hF]
          exact ⟨hηH, hηK⟩
        exact absurd hmem (hLT.extendFrom_not_mem hU hU0 hS₀ hS₀T h.symm)
    rw [← hF, extendFrom_H_eq (continuousOn_fwdMapInv hU hU0 hS₀) hγH,
      QuantumZipper.RS.fwdMap_fwdMapInv hU hU0 hS₀ hγH]
  have hη : Tendsto (fun u => η (S₀ + u)) (𝓝[<] (T - S₀)) (𝓝[H] (x₀ : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hcT : ContinuousWithinAt η (Icc 0 T) T := hc T ⟨by linarith, le_rfl⟩
      have h1 : Tendsto (fun u => S₀ + u) (𝓝[<] (T - S₀)) (𝓝[Icc 0 T] T) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · have hc' : Continuous fun u : ℝ => S₀ + u := continuous_const.add continuous_id
          have := (hc'.tendsto (T - S₀)).mono_left (nhdsWithin_le_nhds (s := Iio (T - S₀)))
          simpa using this
        · filter_upwards [Ioo_mem_nhdsLT hTS] with u hu
          exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
      have := hcT.tendsto.comp h1
      rwa [hx₀] at this
    · filter_upwards [Ioo_mem_nhdsLT hTS] with u hu
      exact hH ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hf := tendsto_fwdMap_of_isForwardSol hU hS₀ hv
  refine (hf.comp hη).congr' ?_
  filter_upwards [Ioo_mem_nhdsLT hTS] with u hu
  exact (hkey u hu.1 hu.2).symm

end Helpers

/-! ### The restarted word through the closed driver -/

section Glued

variable {Ω : Type*} {nL nR ℓ : ℕ} {s : ℝ≥0} {Wj : ℝ≥0 → Ω → ℝ} {E : Set (Ω × HistorySpace 0 0)} {τ : ℝ}
  {τs : ℕ → ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}

/-- **The restarted lifetime at a finite terminal capacity `T`** is `T − S₀`. -/
theorem s3ζ_eq_of_kLife (p : Ω × HistorySpace 0 0) {T : ℝ≥0}
    (hT : (T : WithTop ℝ≥0) = kLife (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p)) :
    s3ζ s Wj E τ p = ((T - s3Start s Wj E τ p : ℝ≥0) : ℝ≥0∞) := by
  classical
  simp only [s3ζ, arcζ, mem_univ, ↓reduceIte, lifeE]
  rw [← hT]
  exact (ENNReal.coe_sub).symm

/-- A finite restarted lifetime comes from a finite terminal capacity. -/
theorem exists_kLife_of_s3ζ (p : Ω × HistorySpace 0 0) {T' : ℝ≥0} (hT' : (T' : ℝ≥0∞) = s3ζ s Wj E τ p) :
    ∃ T : ℝ≥0, (T : WithTop ℝ≥0) = kLife (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p) := by
  classical
  have hne : (kLife (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p) : ℝ≥0∞) ≠ ⊤ := by
    intro htop
    have h : s3ζ s Wj E τ p = ⊤ := by
      simp only [s3ζ, arcζ, mem_univ, ↓reduceIte, lifeE]
      rw [htop]
      exact ENNReal.top_sub_coe
    rw [h] at hT'
    exact ENNReal.coe_ne_top hT'
  obtain ⟨T, hT⟩ := WithTop.ne_top_iff_exists.1 hne
  exact ⟨T, hT⟩

variable {U : ℝ → ℝ} {T : ℝ≥0}

/-- Before the restarted lifetime, the restarted driver is the shifted closed driver. -/
theorem s3W_eq_shiftDrv (p : Ω × HistorySpace 0 0)
    (hT : (T : WithTop ℝ≥0) = kLife (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p))
    (hEq : EqOn (kPath (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p)) U (Ico 0 (T : ℝ)))
    {r : ℝ≥0} (hr : s3Start s Wj E τ p + r < T) : s3W s Wj E τ r p = shiftDrv U (s3Start s Wj E τ p) r := by
  have hlt : ((s3Start s Wj E τ p + r : ℝ≥0) : WithTop ℝ≥0) <
      kLife (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p) := by
    rw [← hT]
    exact_mod_cast hr
  have hS : s3Start s Wj E τ p < T := lt_of_le_of_lt le_self_add hr
  simp only [s3W]
  rw [arcW_of_lt (lt_arcζ_iff.2 ⟨mem_univ _, hlt⟩), ← kPath_coe, ← kPath_coe,
    hEq ⟨by positivity, by exact_mod_cast hr⟩, hEq ⟨by positivity, by exact_mod_cast hS⟩]
  simp only [shiftDrv, NNReal.coe_add]

/-- Before the restarted lifetime, the restarted left marks are the reflected images of their initial values under
the shifted closed driver. -/
theorem s6VL_eq_rightImg (p : Ω × HistorySpace 0 0) (hU : Continuous U)
    (hT : (T : WithTop ℝ≥0) = kLife (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p))
    (hEq : EqOn (kPath (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p)) U (Ico 0 (T : ℝ)))
    {r : ℝ≥0} (hr : s3Start s Wj E τ p + r < T) (i : Fin ((nL + 1) + ℓ)) :
    s6VL xL τs ℓ s Wj E τ i r p = -rightImg (shiftDrv (fun s => -U s) (s3Start s Wj E τ p))
      (-s3XL xL τs ℓ s Wj E τ p (treeIdx ℓ (nL + 1) i)) r := by
  have hlt : ((s3Start s Wj E τ p + r : ℝ≥0) : WithTop ℝ≥0) <
      kLife (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p) := by
    rw [← hT]
    exact_mod_cast hr
  have hEq' : EqOn (kPath (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p)) U
      (Icc 0 ((s3Start s Wj E τ p + r : ℝ≥0) : ℝ)) := fun x hx => hEq ⟨hx.1, lt_of_le_of_lt hx.2 (by exact_mod_cast hr)⟩
  have hd := arcVL_sub_arcW (Al := univ) (xL := s3XL xL τs ℓ s Wj E τ) (mem_univ p) hlt hU hEq'
    (treeIdx ℓ (nL + 1) i)
  have hW := s3W_eq_shiftDrv (τ := τ) p hT hEq hr
  simp only [s3W] at hW
  simp only [s6VL, s3VL]
  linarith

/-- Before the restarted lifetime, the restarted right marks are the images of their initial values under the
shifted closed driver. -/
theorem s6VR_eq_rightImg (p : Ω × HistorySpace 0 0) (hU : Continuous U)
    (hT : (T : WithTop ℝ≥0) = kLife (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p))
    (hEq : EqOn (kPath (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p)) U (Ico 0 (T : ℝ)))
    {r : ℝ≥0} (hr : s3Start s Wj E τ p + r < T) (j : Fin ((nR + 1) + ℓ)) :
    s6VR xR τs ℓ s Wj E τ j r p = rightImg (shiftDrv U (s3Start s Wj E τ p))
      (s3XR xR τs ℓ s Wj E τ p (treeIdx ℓ (nR + 1) j)) r := by
  have hlt : ((s3Start s Wj E τ p + r : ℝ≥0) : WithTop ℝ≥0) <
      kLife (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p) := by
    rw [← hT]
    exact_mod_cast hr
  have hEq' : EqOn (kPath (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p)) U
      (Icc 0 ((s3Start s Wj E τ p + r : ℝ≥0) : ℝ)) := fun x hx => hEq ⟨hx.1, lt_of_le_of_lt hx.2 (by exact_mod_cast hr)⟩
  have hd := arcVR_sub_arcW (Al := univ) (xR := s3XR xR τs ℓ s Wj E τ) (mem_univ p) hlt hU hEq'
    (treeIdx ℓ (nR + 1) j)
  have hW := s3W_eq_shiftDrv (τ := τ) p hT hEq hr
  simp only [s3W] at hW
  simp only [s6VR, s3VR]
  linarith

/-- The tree index of the last left mark is the root junction. -/
theorem treeIdx_far {n : ℕ} {i : Fin ((n + 1) + ℓ)} (hi : (i : ℕ) = n + ℓ) :
    treeIdx ℓ (n + 1) i = Fin.natAdd ℓ (Fin.last n) := by
  rw [treeIdx_of_ge (by omega)]
  ext
  simp only [Fin.val_natAdd, Fin.val_last]
  omega

/-- **The initial far left mark of the restarted word** on the alive event: the left junction flowed to `S₀` under any
continuous driver agreeing with the chain driver on `[0, S₀]`. -/
theorem s3XL_far_eq (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) {p : Ω × HistorySpace 0 0}
    (hp : p ∈ s3Alive s Wj E τ) (hτs : ∀ j : Fin ℓ, 0 ≤ τs (j + 1) ∧ τs (j + 1) ≤ τ) (hU : Continuous U)
    (hEq : EqOn (kPath (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p)) U
      (Icc 0 (s3Start s Wj E τ p : ℝ))) {i : Fin ((nL + 1) + ℓ)} (hi : (i : ℕ) = nL + ℓ) :
    s3XL xL τs ℓ s Wj E τ p (treeIdx ℓ (nL + 1) i) =
      -rightImg (fun r => -U r) (-GlueImg.imgMarkL xL (cfDrv0 s p.2) s (Fin.last nL)) (s3Start s Wj E τ p)
        - U (s3Start s Wj E τ p) := by
  classical
  rw [treeIdx_far hi]
  simp only [s3XL, hp, ↓reduceIte]
  rw [imgStageVL_congr hU hEq xL _ _ (s3_switch hEg hp hτs) (s3Start s Wj E τ p).coe_nonneg]
  simp only [imgStageVL, Fin.append_right, rootVL]

/-- **The initial far right mark of the restarted word** on the alive event. -/
theorem s3XR_far_eq (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) {p : Ω × HistorySpace 0 0}
    (hp : p ∈ s3Alive s Wj E τ) (hτs : ∀ j : Fin ℓ, 0 ≤ τs (j + 1) ∧ τs (j + 1) ≤ τ) (hU : Continuous U)
    (hEq : EqOn (kPath (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p)) U
      (Icc 0 (s3Start s Wj E τ p : ℝ))) {j : Fin ((nR + 1) + ℓ)} (hj : (j : ℕ) = nR + ℓ) :
    s3XR xR τs ℓ s Wj E τ p (treeIdx ℓ (nR + 1) j) =
      rightImg U (GlueImg.imgMarkR xR (cfDrv0 s p.2) s (Fin.last nR)) (s3Start s Wj E τ p)
        - U (s3Start s Wj E τ p) := by
  classical
  rw [treeIdx_far hj]
  simp only [s3XR, hp, ↓reduceIte]
  rw [imgStageVR_congr hU hEq xR _ _ (s3_switch hEg hp hτs) (s3Start s Wj E τ p).coe_nonneg]
  simp only [imgStageVR, Fin.append_right, rootVR]

/-- **The killing of the restarted word at its far marks, with left limits** (`IsKilledAtFarLim`), on a good alive
sample with a strictly ordered restarted start, given that the full staged image arc exits at a finite terminal
capacity through a real point beyond the left junction or beyond the right junction. -/
theorem isKilledAtFarLim_s6 (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) {p : Ω × HistorySpace 0 0}
    (hp : p ∈ s3Alive s Wj E τ) (hxL : ∀ i, xL i ≤ 0) (hxLa : Antitone xL) (hxR : ∀ j, 0 ≤ xR j)
    (hxRm : Monotone xR) (hτs : ∀ j : Fin ℓ, 0 ≤ τs (j + 1) ∧ τs (j + 1) ≤ τ)
    (hτm : Monotone fun j : Fin ℓ => τs (j + 1)) (hℓ : 0 < ℓ)
    (hsA : StrictAnti fun i => s6VL xL τs ℓ s Wj E τ i 0 p)
    (hsM : StrictMono fun j => s6VR xR τs ℓ s Wj E τ j 0 p)
    {iL : Fin ((nL + 1) + ℓ)} (hiL : (iL : ℕ) = nL + ℓ) {iR : Fin ((nR + 1) + ℓ)} (hiR : (iR : ℕ) = nR + ℓ)
    (hexit : ∀ T : ℝ≥0, (T : WithTop ℝ≥0) = kLife (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p) →
      ∃ x₀ : ℝ, Tendsto (kTrace (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p)) (𝓝[<] T)
          (𝓝 (x₀ : ℂ)) ∧
        (x₀ < GlueImg.imgMarkL xL (cfDrv0 s p.2) s (Fin.last nL) ∨
          GlueImg.imgMarkR xR (cfDrv0 s p.2) s (Fin.last nR) < x₀)) :
    StagedKCand.IsKilledAtFarLim iL iR (s3W s Wj E τ · p) (fun i t => s6VL xL τs ℓ s Wj E τ i t p)
      (fun j t => s6VR xR τs ℓ s Wj E τ j t p) (s3ζ s Wj E τ p) := by
  have hγ := isKilledArc_gCurve hEg p
  have hK := isKilledWord_s6 hEg hxL hxLa hxR hxRm hτs hτm
  set γ := gCurve s (fun _ => ⊤) Wj E p with hγdef
  set P := gPre s (fun _ => ⊤) Wj E p with hPdef
  set S₀ := s3Start s Wj E τ p with hS₀def
  have hS₀ : (S₀ : WithTop ℝ≥0) < kLife γ P := StagedS5.s3Start_lt_kLife' hEg τ p
  have hW0 : s3W s Wj E τ 0 p = 0 := StagedS6.arcW_zero p
  have h0L : s6VL xL τs ℓ s Wj E τ iL 0 p < s3W s Wj E τ 0 p := by
    have hlt : (⟨0, by omega⟩ : Fin ((nL + 1) + ℓ)) < iL := by
      rw [Fin.lt_def]
      simp only
      omega
    have h1 := hsA hlt
    have h2 : s6VL xL τs ℓ s Wj E τ ⟨0, by omega⟩ 0 p ≤ 0 := by
      rw [s6VL_zero hEg hτs p]
      exact s3XL_nonpos hEg hτs p _
    rw [hW0]
    exact lt_of_lt_of_le h1 h2
  have h0R : s3W s Wj E τ 0 p < s6VR xR τs ℓ s Wj E τ iR 0 p := by
    have hlt : (⟨0, by omega⟩ : Fin ((nR + 1) + ℓ)) < iR := by
      rw [Fin.lt_def]
      simp only
      omega
    have h1 := hsM hlt
    have h2 : 0 ≤ s6VR xR τs ℓ s Wj E τ ⟨0, by omega⟩ 0 p := by
      rw [s6VR_zero hEg hτs p]
      exact s3XR_nonneg hEg hτs p _
    rw [hW0]
    exact lt_of_le_of_lt h2 h1
  refine ⟨StagedS6.zero_lt_arcζ (fun p => StagedS5.s3Start_lt_kLife' hEg τ p) p, fun t ht => ?_,
    fun T' hT' => ?_⟩
  · rcases eq_zero_or_pos t with rfl | ht0
    · exact ⟨h0L.ne', h0R.ne⟩
    · exact ⟨(hK.sepL p t ht0 ht iL).ne', (hK.sepR p t ht0 ht iR).ne⟩
  obtain ⟨T, hT⟩ := exists_kLife_of_s3ζ (τ := τ) p hT'
  have hζ := s3ζ_eq_of_kLife (τ := τ) p hT
  have hT'eq : T' = T - S₀ := by
    rw [hζ] at hT'
    exact_mod_cast hT'
  have hS₀T : S₀ < T := by
    have := hS₀
    rw [← hT] at this
    exact_mod_cast this
  have hT0 : 0 < T := lt_of_le_of_lt zero_le hS₀T
  have : (𝓝[<] T).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hT0⟩
  obtain ⟨x₀, hlim, hside⟩ := hexit T hT
  obtain ⟨-, -, hjL, hjR, -⟩ := hEg p hp.1
  have hc := continuous_cfDrv0 s p.2
  have hmL : ∀ k, GlueImg.imgMarkL xL (cfDrv0 s p.2) s k ≤ 0 :=
    snoc_le (fun i => psiL_nonpos hc s.coe_nonneg hjL (hxL i))
      ((junL_le_psiL hc s.coe_nonneg hjL le_rfl).trans (psiL_nonpos hc s.coe_nonneg hjL le_rfl))
  have hmR : ∀ k, 0 ≤ GlueImg.imgMarkR xR (cfDrv0 s p.2) s k :=
    le_snoc (fun j => psiR_nonneg hc s.coe_nonneg hjR (hxR j))
      ((psiR_nonneg hc s.coe_nonneg hjR le_rfl).trans (psiR_le_junR hc s.coe_nonneg hjR le_rfl))
  have hx₀ : x₀ ≠ 0 := by
    rcases hside with h | h
    · linarith [hmL (Fin.last nL)]
    · linarith [hmR (Fin.last nR)]
  obtain ⟨U, hU, -, hEq, -⟩ := KillArc.exists_closed_driver_ne hγ hT0 hT hx₀ hlim
  have hUn : Continuous fun r => -U r := hU.neg
  have hEqS : EqOn (kPath γ P) U (Icc 0 (S₀ : ℝ)) := fun r hr =>
    hEq ⟨hr.1, lt_of_le_of_lt hr.2 (by exact_mod_cast hS₀T)⟩
  have hr : ∀ r : ℝ≥0, r < T' → S₀ + r < T := fun r hr' => by
    rw [hT'eq] at hr'
    exact (lt_tsub_iff_left).1 hr'
  have hST : (S₀ : ℝ) + T' = T := by
    rw [hT'eq, NNReal.coe_sub hS₀T.le]
    ring
  have hVc : Continuous (shiftDrv (fun s => -U s) (S₀ : ℝ)) := continuous_shiftDrv hUn _
  have hWc : Continuous (shiftDrv U (S₀ : ℝ)) := continuous_shiftDrv hU _
  -- the full driver and the full junctions at `T`
  have hkW : Tendsto (kW γ P) (𝓝[<] T) (𝓝 (U T)) := tendsto_nhdsLT_of_eq hU.continuousOn fun r hr' => by
    rw [← kPath_coe]
    exact hEq ⟨r.2, by exact_mod_cast hr'⟩
  have hkVL : ∀ a : ℝ, Tendsto (kVL γ P (fun _ : Fin 1 => a) 0) (𝓝[<] T)
      (𝓝 (-rightImg (fun r => -U r) (-a) T)) := fun a =>
    tendsto_nhdsLT_of_eq (f := fun r => -rightImg (fun r => -U r) (-a) r) (continuousOn_rightImg hUn _).neg
      fun r hr' => by
        have hlt : (r : WithTop ℝ≥0) < kLife γ P := by
          rw [← hT]
          exact_mod_cast hr'
        rw [kVL_of_lt _ _ hlt]
        simp only [kVLr]
        rw [kImg_eq hUn (fun x hx => by simp only [hEq ⟨hx.1, lt_of_le_of_lt hx.2 (by exact_mod_cast hr')⟩])
          le_rfl]
  refine ⟨shiftDrv U S₀ T', fun i => -rightImg (shiftDrv (fun s => -U s) S₀)
      (-s3XL xL τs ℓ s Wj E τ p (treeIdx ℓ (nL + 1) i)) T',
    fun j => rightImg (shiftDrv U S₀) (s3XR xR τs ℓ s Wj E τ p (treeIdx ℓ (nR + 1) j)) T',
    tendsto_nhdsLT_of_eq hWc.continuousOn fun r hr' => s3W_eq_shiftDrv p hT hEq (hr r hr'),
    fun i => tendsto_nhdsLT_of_eq (continuousOn_rightImg hVc _).neg fun r hr' =>
      s6VL_eq_rightImg p hU hT hEq (hr r hr') i,
    fun j => tendsto_nhdsLT_of_eq (continuousOn_rightImg hWc _) fun r hr' =>
      s6VR_eq_rightImg p hU hT hEq (hr r hr') j, ?_⟩
  rcases hside with hx | hx
  · left
    obtain ⟨w₀', vL₀', -, hw', hvL', -, hL', -⟩ := KillArc.killedArc_swallow hγ
      (GlueImg.imgMarkL xL (cfDrv0 s p.2) s) (GlueImg.imgMarkR xR (cfDrv0 s p.2) s) hmL hmR hT (Or.inl hx) hlim
    have e1 : w₀' = U T := tendsto_nhds_unique hw' hkW
    have e2 : vL₀' (Fin.last nL) =
        -rightImg (fun r => -U r) (-GlueImg.imgMarkL xL (cfDrv0 s p.2) s (Fin.last nL)) T := by
      refine tendsto_nhds_unique (hvL' _) ?_
      exact hkVL (GlueImg.imgMarkL xL (cfDrv0 s p.2) s (Fin.last nL))
    have e3 := hL' hx
    have hrel := StagedS3.relL_shift hU S₀.coe_nonneg T'.coe_nonneg
      (-GlueImg.imgMarkL xL (cfDrv0 s p.2) s (Fin.last nL))
    rw [hST] at hrel
    beta_reduce
    rw [s3XL_far_eq hEg hp hτs hU hEqS hiL]
    linarith
  · right
    obtain ⟨w₀', -, vR₀', hw', -, hvR', -, hR'⟩ := KillArc.killedArc_swallow hγ
      (GlueImg.imgMarkL xL (cfDrv0 s p.2) s) (GlueImg.imgMarkR xR (cfDrv0 s p.2) s) hmL hmR hT (Or.inr hx) hlim
    have e1 : w₀' = U T := tendsto_nhds_unique hw' hkW
    have e2 : vR₀' (Fin.last nR) = rightImg U (GlueImg.imgMarkR xR (cfDrv0 s p.2) s (Fin.last nR)) T := by
      refine tendsto_nhds_unique (hvR' _) (tendsto_nhdsLT_of_eq (continuousOn_rightImg hU _) fun r hr' => ?_)
      have hlt : (r : WithTop ℝ≥0) < kLife γ P := by
        rw [← hT]
        exact_mod_cast hr'
      rw [kVR_of_lt _ _ hlt]
      simp only [kVRr]
      rw [kImg_eq hU (fun x hx => hEq ⟨hx.1, lt_of_le_of_lt hx.2 (by exact_mod_cast hr')⟩) le_rfl]
    have e3 := hR' hx
    have hrel := StagedS3.relR_shift hU S₀.coe_nonneg T'.coe_nonneg
      (GlueImg.imgMarkR xR (cfDrv0 s p.2) s (Fin.last nR))
    rw [hST] at hrel
    beta_reduce
    rw [s3XR_far_eq hEg hp hτs hU hEqS hiR]
    linarith

/-- **The restarted driver has a generating trace up to its lifetime** when the full staged image arc exits at a
finite terminal capacity through a nonzero real point: the shifted Loewner tips of the closed driver, frozen at their
limit `f_{S₀}(x₀)`. -/
theorem exists_isGeneratingTrace_s3W (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) (p : Ω × HistorySpace 0 0)
    (hT : (T : WithTop ℝ≥0) = kLife (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p))
    {x₀ : ℝ} (hx₀ : x₀ ≠ 0)
    (hlim : Tendsto (kTrace (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p)) (𝓝[<] T)
      (𝓝 (x₀ : ℂ))) :
    ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (s3W s Wj E τ · p) (s3ζ s Wj E τ p) η := by
  have hγ := isKilledArc_gCurve hEg p
  set γ := gCurve s (fun _ => ⊤) Wj E p with hγdef
  set P := gPre s (fun _ => ⊤) Wj E p with hPdef
  set S₀ := s3Start s Wj E τ p with hS₀def
  have hS₀ : (S₀ : WithTop ℝ≥0) < kLife γ P := StagedS5.s3Start_lt_kLife' hEg τ p
  have hS₀T : S₀ < T := by
    have := hS₀
    rw [← hT] at this
    exact_mod_cast this
  have hT0 : 0 < T := lt_of_le_of_lt zero_le hS₀T
  obtain ⟨U, hU, hU0, hEq, hLT⟩ := KillArc.exists_closed_driver_ne hγ hT0 hT hx₀ hlim
  obtain ⟨hc, hinj, -, hH, -⟩ := KillArc.closedKTrace_spec_ne hγ hT0 hT hx₀ hlim
  obtain ⟨S, -, -, hS₀S, w, hw, hw0, hEqw, η', hη'L, hη'P, -⟩ := hγ.exists_kPath_trace hS₀
  obtain ⟨v, hv⟩ := exists_isForwardSol_of_isProperArc hη'L hη'P hw hw0 hx₀ S₀.coe_nonneg
  have hvU : QuantumZipper.IsForwardSol U x₀ S₀ v := QuantumZipper.isForwardSol_congr_drive (fun r hr =>
    (hEqw ⟨hr.1, hr.2.trans hS₀S.le⟩).symm.trans (hEq ⟨hr.1, lt_of_le_of_lt hr.2 (by exact_mod_cast hS₀T)⟩)) hv
  have hL := tendsto_shiftTip hU hU0 S₀.coe_nonneg (by exact_mod_cast hS₀T) hLT hc hinj hH
    (closedKTrace_end γ P T x₀) hvU
  obtain ⟨hLTs, -⟩ := hLT.isLoewnerTraceLT_shift hU hU0 S₀.coe_nonneg
  have hcoe : ((T - S₀ : ℝ≥0) : ℝ) = (T : ℝ) - S₀ := NNReal.coe_sub hS₀T.le
  rw [s3ζ_eq_of_kLife (τ := τ) p hT]
  refine ⟨_, isGeneratingTrace_of_isLoewnerTraceLT (tsub_pos_of_lt hS₀T) (V := shiftDrive U S₀)
    (by rw [hcoe]; exact hLTs) (fun r hr0 hrT => ?_) (by rw [hcoe]; exact hL)⟩
  have hr1 : r.toNNReal < T - S₀ := by
    rw [Real.toNNReal_lt_iff_lt_coe hr0]
    exact hrT
  rw [s3W_eq_shiftDrv p hT hEq ((lt_tsub_iff_left).1 hr1), Real.coe_toNNReal _ hr0]
  rfl

/-- **The restarted far left mark is the flowed left junction** (relative to the driver): before the restarted
lifetime, on the alive event, `V_far(t) − W(t)` is the full arc's killed image of the left junction relative to the
full driver at `S₀ + t`. -/
theorem s6VL_far_sub (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) {p : Ω × HistorySpace 0 0}
    (hp : p ∈ s3Alive s Wj E τ) (hτs : ∀ j : Fin ℓ, 0 ≤ τs (j + 1) ∧ τs (j + 1) ≤ τ)
    {iL : Fin ((nL + 1) + ℓ)} (hiL : (iL : ℕ) = nL + ℓ) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < s3ζ s Wj E τ p) :
    s6VL xL τs ℓ s Wj E τ iL t p - s3W s Wj E τ t p =
      -kImg (fun r => -kPath (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p) r)
          (-GlueImg.imgMarkL xL (cfDrv0 s p.2) s (Fin.last nL)) (s3Start s Wj E τ p + t) -
        kW (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p) (s3Start s Wj E τ p + t) := by
  have hγ := isKilledArc_gCurve hEg p
  set γ := gCurve s (fun _ => ⊤) Wj E p with hγdef
  set P := gPre s (fun _ => ⊤) Wj E p with hPdef
  set S₀ := s3Start s Wj E τ p with hS₀def
  have hlt : ((S₀ + t : ℝ≥0) : WithTop ℝ≥0) < kLife γ P := (lt_arcζ_iff.1 ht).2
  obtain ⟨S, -, -, htS, w, hw, -, hEq, -⟩ := hγ.exists_kPath_trace hlt
  have hEq' : EqOn (kPath γ P) w (Icc 0 ((S₀ + t : ℝ≥0) : ℝ)) := hEq.mono (Icc_subset_Icc_right htS.le)
  have hEqS : EqOn (kPath γ P) w (Icc 0 (S₀ : ℝ)) :=
    hEq'.mono (Icc_subset_Icc_right (by exact_mod_cast le_self_add))
  have hwn : Continuous fun r => -w r := hw.neg
  have hd := arcVL_sub_arcW (γ := gCurve s (fun _ => ⊤) Wj E) (P := gPre s (fun _ => ⊤) Wj E)
    (S₀ := s3Start s Wj E τ) (Al := univ) (xL := s3XL xL τs ℓ s Wj E τ) (mem_univ p) hlt hw hEq'
    (treeIdx ℓ (nL + 1) iL)
  have hx := s3XL_far_eq (xL := xL) hEg hp hτs hw hEqS hiL
  have hrel := StagedS3.relL_shift hw S₀.coe_nonneg t.coe_nonneg (-GlueImg.imgMarkL xL (cfDrv0 s p.2) s (Fin.last nL))
  have hk : kImg (fun r => -kPath γ P r) (-GlueImg.imgMarkL xL (cfDrv0 s p.2) s (Fin.last nL)) (S₀ + t) =
      rightImg (fun r => -w r) (-GlueImg.imgMarkL xL (cfDrv0 s p.2) s (Fin.last nL)) ((S₀ + t : ℝ≥0) : ℝ) :=
    kImg_eq hwn (fun r hr => by simp only [hEq' hr]) le_rfl _
  have hkW : kW γ P (S₀ + t) = w ((S₀ + t : ℝ≥0) : ℝ) := by
    rw [← kPath_coe]
    exact hEq' ⟨by positivity, le_rfl⟩
  simp only [s6VL, s3VL, s3W]
  rw [hd, hx, hrel, hk, hkW, NNReal.coe_add]

/-- **The restarted far right mark is the flowed right junction** (relative to the driver). -/
theorem s6VR_far_sub (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) {p : Ω × HistorySpace 0 0}
    (hp : p ∈ s3Alive s Wj E τ) (hτs : ∀ j : Fin ℓ, 0 ≤ τs (j + 1) ∧ τs (j + 1) ≤ τ)
    {iR : Fin ((nR + 1) + ℓ)} (hiR : (iR : ℕ) = nR + ℓ) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < s3ζ s Wj E τ p) :
    s6VR xR τs ℓ s Wj E τ iR t p - s3W s Wj E τ t p =
      kImg (kPath (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p))
          (GlueImg.imgMarkR xR (cfDrv0 s p.2) s (Fin.last nR)) (s3Start s Wj E τ p + t) -
        kW (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p) (s3Start s Wj E τ p + t) := by
  have hγ := isKilledArc_gCurve hEg p
  set γ := gCurve s (fun _ => ⊤) Wj E p with hγdef
  set P := gPre s (fun _ => ⊤) Wj E p with hPdef
  set S₀ := s3Start s Wj E τ p with hS₀def
  have hlt : ((S₀ + t : ℝ≥0) : WithTop ℝ≥0) < kLife γ P := (lt_arcζ_iff.1 ht).2
  obtain ⟨S, -, -, htS, w, hw, -, hEq, -⟩ := hγ.exists_kPath_trace hlt
  have hEq' : EqOn (kPath γ P) w (Icc 0 ((S₀ + t : ℝ≥0) : ℝ)) := hEq.mono (Icc_subset_Icc_right htS.le)
  have hEqS : EqOn (kPath γ P) w (Icc 0 (S₀ : ℝ)) :=
    hEq'.mono (Icc_subset_Icc_right (by exact_mod_cast le_self_add))
  have hd := arcVR_sub_arcW (γ := gCurve s (fun _ => ⊤) Wj E) (P := gPre s (fun _ => ⊤) Wj E)
    (S₀ := s3Start s Wj E τ) (Al := univ) (xR := s3XR xR τs ℓ s Wj E τ) (mem_univ p) hlt hw hEq'
    (treeIdx ℓ (nR + 1) iR)
  have hx := s3XR_far_eq (xR := xR) hEg hp hτs hw hEqS hiR
  have hrel := StagedS3.relR_shift hw S₀.coe_nonneg t.coe_nonneg (GlueImg.imgMarkR xR (cfDrv0 s p.2) s (Fin.last nR))
  have hk : kImg (kPath γ P) (GlueImg.imgMarkR xR (cfDrv0 s p.2) s (Fin.last nR)) (S₀ + t) =
      rightImg w (GlueImg.imgMarkR xR (cfDrv0 s p.2) s (Fin.last nR)) ((S₀ + t : ℝ≥0) : ℝ) :=
    kImg_eq hw hEq' le_rfl _
  have hkW : kW γ P (S₀ + t) = w ((S₀ + t : ℝ≥0) : ℝ) := by
    rw [← kPath_coe]
    exact hEq' ⟨by positivity, le_rfl⟩
  simp only [s6VR, s3VR, s3W]
  rw [hd, hx, hrel, hk, hkW, NNReal.coe_add]

/-- **The killed trace of the full staged image arc does not converge into `ℍ`** at a finite terminal capacity, on
good samples (the flow line would end off the counterflow hull; the template's `notMem_H_of_tendsto_kTrace`). -/
theorem notMem_H_of_tendsto_gCurve {p : Ω × HistorySpace 0 0} (hpE : p ∈ E) (hg : IsGood49 s (fun _ => ⊤) Wj p)
    {T : ℝ≥0} (hT : (T : WithTop ℝ≥0) = kLife (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p))
    {z : ℂ} (hz : Tendsto (kTrace (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p)) (𝓝[<] T) (𝓝 z)) :
    z ∉ H := by
  obtain ⟨hα, hG, -, -, hQ⟩ := hg
  have e1 : gCurve s (fun _ => ⊤) Wj E p = imgCurve (cfDrv0 s p.2) s (seedLine (fun _ => ⊤) Wj p.1) :=
    Word49.gCurve_of_mem hpE
  have e2 : gPre s (fun _ => ⊤) Wj E p =
      preContact (seedLine (fun _ => ⊤) Wj p.1) (negInv '' fwdHull (cfDrv0 s p.2) s) := by
    rw [Word49.gPre_of_mem hpE, hQ]
  rw [e1, e2] at hT hz
  exact StagedRep.notMem_H_of_tendsto_kTrace (continuous_cfDrv0 s p.2) (cfDrv0_zero s p.2) s.coe_nonneg hG hα hT hz

end Glued

end InteractingSLE.Sec5.CrossCond.StagedS7
