/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedNodeStart
import InteractingSLE.Spec.Sec5.StagedS3Shift
import InteractingSLE.Spec.Sec5.CrossCondStagedFinalPast
import InteractingSLE.Spec.Sec5.GlueCondUnionImgCf

/-!
# Proposition 5.9's tree candidates: one-point arc pieces, strict order of the marks

Packet PROVE-STAGED-NODE. Pathwise facts about the arc pieces of PROVE-PROP59-PIECES' tree candidates, used for
clause 1 of the node laws:

* `arcW_onePt` …: at an alive sample the arc piece (alive set `A`) is the arc piece of the one-point family with
  alive set `univ`;
* **`ArcKilledWordStatement`**: the arc piece of a family of killed arcs with alive set `univ` is a killed word — the
  exact statement of PROVE-STAGED-S6's `StagedS6.isKilledWord_arc` (in flight when this was written; a named input
  here so that it is not proved twice);
* **`arcVL_lt_arcVL`**, **`arcVR_lt_arcVR`**: the real Loewner flow of the restarted chain keeps distinct marks
  strictly ordered (all positive points stay alive under a proper-arc trace);
* `arcVL_zero_eq`, `arcVR_zero_eq`: at time `0` the arc piece's marks are its initial marks;
* **`TreeData.marks_strict`**: on the alive event of every list the tree marks are strictly ordered on their sides of
  the driver (induction along the tree: one new mark on the driver at each switch, at a positive piece time).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Function
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond.StagedNode

open WangWu WangWu.ImgWord MartChar.RealFlow Prop59System Prop59Stage Prop59Pieces Prop59NodeTree GlueImg
open QuantumZipper.RS (shiftDrive)
open Sec7.Lemma71C (capClock)

/-! ### Arc pieces at an alive sample are one-point arc pieces -/

section OnePt

variable {Ω : Type*} {nL nR : ℕ} {γ : Ω → ℝ → ℂ} {P : Ω → Set ℝ} {S₀ : Ω → ℝ≥0} {A : Set Ω} {ω : Ω}

theorem arcW_onePt (hA : ω ∈ A) (u : ℝ≥0) :
    arcW γ P S₀ A u ω = arcW (fun _ : Unit => γ ω) (fun _ => P ω) (fun _ => S₀ ω) univ u () := by
  classical
  simp only [arcW, hA, true_and, mem_univ]

theorem arcζ_onePt (hA : ω ∈ A) :
    arcζ γ P S₀ A ω = arcζ (fun _ : Unit => γ ω) (fun _ => P ω) (fun _ => S₀ ω) univ () := by
  classical
  simp only [arcζ, hA, ↓reduceIte, mem_univ]

theorem realPath_arcW_onePt (hA : ω ∈ A) :
    Bessel.realPath (arcW γ P S₀ A) ω =
      Bessel.realPath (arcW (fun _ : Unit => γ ω) (fun _ => P ω) (fun _ => S₀ ω) univ) () := by
  funext r
  simp only [Bessel.realPath, arcW_onePt hA]

theorem arcVL_onePt (hA : ω ∈ A) (xL : Ω → Fin nL → ℝ) (i : Fin nL) (u : ℝ≥0) :
    arcVL γ P S₀ A xL i u ω =
      arcVL (fun _ : Unit => γ ω) (fun _ => P ω) (fun _ => S₀ ω) univ (fun _ => xL ω) i u () := by
  have e : Bessel.realPath (fun u ω => -arcW γ P S₀ A u ω) ω =
      Bessel.realPath (fun u x => -arcW (fun _ : Unit => γ ω) (fun _ => P ω) (fun _ => S₀ ω) univ u x) () := by
    funext r
    simp only [Bessel.realPath, arcW_onePt hA]
  simp only [arcVL, arcζ_onePt hA, e]

theorem arcVR_onePt (hA : ω ∈ A) (xR : Ω → Fin nR → ℝ) (k : Fin nR) (u : ℝ≥0) :
    arcVR γ P S₀ A xR k u ω =
      arcVR (fun _ : Unit => γ ω) (fun _ => P ω) (fun _ => S₀ ω) univ (fun _ => xR ω) k u () := by
  simp only [arcVR, arcζ_onePt hA, realPath_arcW_onePt hA]

end OnePt

/-! ### The killed word of an arc piece (PROVE-STAGED-S6's statement) -/

/-- **The arc piece of a family of killed arcs is a killed word** (alive set `univ`, initial left marks `≤ 0` antitone,
right marks `≥ 0` monotone): the statement of PROVE-STAGED-S6's `StagedS6.isKilledWord_arc`, as a named input. -/
def ArcKilledWordStatement : Prop :=
  ∀ {Ω : Type} {nL nR : ℕ} {γ : Ω → ℝ → ℂ} {P : Ω → Set ℝ} {S₀ : Ω → ℝ≥0},
    (∀ ω, IsKilledArc (γ ω) (P ω)) → ∀ {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ},
    (∀ ω i, xL ω i ≤ 0) → (∀ ω j, 0 ≤ xR ω j) → (∀ ω, Antitone (xL ω)) → (∀ ω, Monotone (xR ω)) →
    ImgDrv.IsKilledWord (arcW γ P S₀ univ) (arcVL γ P S₀ univ xL) (arcVR γ P S₀ univ xR)
      (fun ω => arcζ γ P S₀ univ ω)

/-! ### Strict order and initial values of the arc marks -/

section Order

variable {Ω : Type*} {nL nR : ℕ} {γ : Ω → ℝ → ℂ} {P : Ω → Set ℝ} {S₀ : Ω → ℝ≥0} {A : Set Ω} {ω : Ω}

theorem shiftDrv_neg_eq' (w : ℝ → ℝ) (S : ℝ) : shiftDrv (fun s => -w s) S = fun s => -shiftDrive w S s := by
  funext s
  simp only [shiftDrv, shiftDrive]
  ring

/-- **Distinct left marks stay strictly ordered** along an arc piece. -/
theorem arcVL_lt_arcVL (hγ : IsKilledArc (γ ω) (P ω)) (hA : ω ∈ A) {xL : Ω → Fin nL → ℝ} {i i' : Fin nL}
    (hx : xL ω i' < xL ω i) (hx0 : xL ω i ≤ 0) {s : ℝ≥0}
    (hs : ((S₀ ω + s : ℝ≥0) : WithTop ℝ≥0) < kLife (γ ω) (P ω)) :
    arcVL γ P S₀ A xL i' s ω < arcVL γ P S₀ A xL i s ω := by
  obtain ⟨S, -, -, htS, w, hw, hw0, hEq, η, hηL, hηP, -⟩ := hγ.exists_kPath_trace hs
  have hEq' : EqOn (kPath (γ ω) (P ω)) w (Icc 0 ((S₀ ω + s : ℝ≥0) : ℝ)) := hEq.mono (Icc_subset_Icc_right htS.le)
  have h1 := StagedS3.arcVL_sub_arcW (xL := xL) hA hs hw hEq' i
  have h2 := StagedS3.arcVL_sub_arcW (xL := xL) hA hs hw hEq' i'
  have hw' : Continuous (shiftDrv (fun s => -w s) (S₀ ω)) := continuous_shiftDrv hw.neg _
  have hη' := StagedLaw.isLoewnerTrace_futureArc hηL hw hw0 (S₀ ω).coe_nonneg
  have hp' := WangWu.isProperArc_futureArc hηL hηP hw hw0 (S₀ ω).coe_nonneg
  have hal := alive_neg_of_isProperArc hη' hp' (QuantumZipper.RS.continuous_shiftDrive hw _)
    (by simp [shiftDrive] : shiftDrive w (S₀ ω : ℝ) 0 = 0) s.coe_nonneg
  rw [← shiftDrv_neg_eq'] at hal
  have hlt := rightImg_lt_gImg_of_lt hw' s.coe_nonneg hal (neg_nonneg.2 hx0) (neg_lt_neg hx)
  rw [← rightImg_eq_gImg hw' s.coe_nonneg (hal _ (by linarith))] at hlt
  linarith

/-- **Distinct right marks stay strictly ordered** along an arc piece. -/
theorem arcVR_lt_arcVR (hγ : IsKilledArc (γ ω) (P ω)) (hA : ω ∈ A) {xR : Ω → Fin nR → ℝ} {k k' : Fin nR}
    (hx : xR ω k < xR ω k') (hx0 : 0 ≤ xR ω k) {s : ℝ≥0}
    (hs : ((S₀ ω + s : ℝ≥0) : WithTop ℝ≥0) < kLife (γ ω) (P ω)) :
    arcVR γ P S₀ A xR k s ω < arcVR γ P S₀ A xR k' s ω := by
  obtain ⟨S, -, -, htS, w, hw, hw0, hEq, η, hηL, hηP, -⟩ := hγ.exists_kPath_trace hs
  have hEq' : EqOn (kPath (γ ω) (P ω)) w (Icc 0 ((S₀ ω + s : ℝ≥0) : ℝ)) := hEq.mono (Icc_subset_Icc_right htS.le)
  have h1 := StagedS3.arcVR_sub_arcW (xR := xR) hA hs hw hEq' k
  have h2 := StagedS3.arcVR_sub_arcW (xR := xR) hA hs hw hEq' k'
  have hw' : Continuous (shiftDrv w (S₀ ω)) := continuous_shiftDrv hw _
  have hη' := StagedLaw.isLoewnerTrace_futureArc hηL hw hw0 (S₀ ω).coe_nonneg
  have hp' := WangWu.isProperArc_futureArc hηL hηP hw hw0 (S₀ ω).coe_nonneg
  have hal := alive_of_isProperArc hη' hp' (QuantumZipper.RS.continuous_shiftDrive hw _)
    (by simp [shiftDrive] : shiftDrive w (S₀ ω : ℝ) 0 = 0) s.coe_nonneg
  have e : shiftDrive w (S₀ ω) = shiftDrv w (S₀ ω) := rfl
  rw [e] at hal
  have hlt := rightImg_lt_gImg_of_lt hw' s.coe_nonneg hal hx0 hx
  rw [← rightImg_eq_gImg hw' s.coe_nonneg (hal _ (by linarith))] at hlt
  linarith

theorem arcW_zero' (ω : Ω) : arcW γ P S₀ A 0 ω = 0 := by
  classical
  simp only [arcW, add_zero, sub_self, ite_self]

/-- At time `0` the left marks of an alive arc piece are its initial marks. -/
theorem arcVL_zero_eq (hγ : IsKilledArc (γ ω) (P ω)) (hA : ω ∈ A) {xL : Ω → Fin nL → ℝ} {i : Fin nL}
    (hx0 : xL ω i ≤ 0) (hs : ((S₀ ω : ℝ≥0) : WithTop ℝ≥0) < kLife (γ ω) (P ω)) :
    arcVL γ P S₀ A xL i 0 ω = xL ω i := by
  have hs' : ((S₀ ω + 0 : ℝ≥0) : WithTop ℝ≥0) < kLife (γ ω) (P ω) := by rwa [add_zero]
  obtain ⟨S, -, -, htS, w, hw, hw0, hEq, -⟩ := hγ.exists_kPath_trace hs'
  have hEq' : EqOn (kPath (γ ω) (P ω)) w (Icc 0 ((S₀ ω + 0 : ℝ≥0) : ℝ)) := hEq.mono (Icc_subset_Icc_right htS.le)
  have h1 := StagedS3.arcVL_sub_arcW (xL := xL) hA hs' hw hEq' i
  have hw' : Continuous (shiftDrv (fun s => -w s) (S₀ ω)) := continuous_shiftDrv hw.neg _
  rw [arcW_zero', NNReal.coe_zero, rightImg_zero hw' (shiftDrv_zero _) (neg_nonneg.2 hx0), shiftDrv_zero] at h1
  linarith

/-- At time `0` the right marks of an alive arc piece are its initial marks. -/
theorem arcVR_zero_eq (hγ : IsKilledArc (γ ω) (P ω)) (hA : ω ∈ A) {xR : Ω → Fin nR → ℝ} {k : Fin nR}
    (hx0 : 0 ≤ xR ω k) (hs : ((S₀ ω : ℝ≥0) : WithTop ℝ≥0) < kLife (γ ω) (P ω)) :
    arcVR γ P S₀ A xR k 0 ω = xR ω k := by
  have hs' : ((S₀ ω + 0 : ℝ≥0) : WithTop ℝ≥0) < kLife (γ ω) (P ω) := by rwa [add_zero]
  obtain ⟨S, -, -, htS, w, hw, hw0, hEq, -⟩ := hγ.exists_kPath_trace hs'
  have hEq' : EqOn (kPath (γ ω) (P ω)) w (Icc 0 ((S₀ ω + 0 : ℝ≥0) : ℝ)) := hEq.mono (Icc_subset_Icc_right htS.le)
  have h1 := StagedS3.arcVR_sub_arcW (xR := xR) hA hs' hw hEq' k
  have hw' : Continuous (shiftDrv w (S₀ ω)) := continuous_shiftDrv hw _
  rw [arcW_zero', NNReal.coe_zero, rightImg_zero hw' (shiftDrv_zero _) hx0, shiftDrv_zero] at h1
  linarith

end Order

/-! ### Strict order of the tree marks on the alive events -/

section Tree

theorem strictAnti_cons {n : ℕ} {a : ℝ} {v : Fin n → ℝ} (hv : StrictAnti v) (ha : ∀ i, v i < a) :
    StrictAnti (Fin.cons a v : Fin (n + 1) → ℝ) := by
  intro i i' hii
  induction i using Fin.cases with
  | zero =>
    induction i' using Fin.cases with
    | zero => exact absurd hii (lt_irrefl _)
    | succ i' => simpa only [Fin.cons_zero, Fin.cons_succ] using ha i'
  | succ i =>
    induction i' using Fin.cases with
    | zero => exact absurd hii (Fin.not_lt_zero _)
    | succ i' =>
      simp only [Fin.cons_succ]
      exact hv (Fin.succ_lt_succ_iff.1 hii)

theorem strictMono_cons {n : ℕ} {a : ℝ} {v : Fin n → ℝ} (hv : StrictMono v) (ha : ∀ i, a < v i) :
    StrictMono (Fin.cons a v : Fin (n + 1) → ℝ) := by
  intro i i' hii
  induction i using Fin.cases with
  | zero =>
    induction i' using Fin.cases with
    | zero => exact absurd hii (lt_irrefl _)
    | succ i' => simpa only [Fin.cons_zero, Fin.cons_succ] using ha i'
  | succ i =>
    induction i' using Fin.cases with
    | zero => exact absurd hii (Fin.not_lt_zero _)
    | succ i' =>
      simp only [Fin.cons_succ]
      exact hv (Fin.succ_lt_succ_iff.1 hii)

variable {Ω : Type*} [MeasurableSpace Ω] {nL₀ nR₀ : ℕ} {D : TreeData Ω nL₀ nR₀}

/-- The ordered strict marks of a list. -/
def MarksStrict (xL : Fin nL₀ → ℝ) (xR : Fin nR₀ → ℝ) : Prop :=
  (∀ i, xL i ≤ 0) ∧ StrictAnti xL ∧ (∀ k, 0 ≤ xR k) ∧ StrictMono xR

/-- **The tree marks are strictly ordered on the alive events**: the root marks are, and at each switch (a positive
piece time before the parent's lifetime) the parent's marks move strictly left (right) of the driver, keep their
strict order, and one new mark is born on the driver on each side. -/
theorem TreeData.marks_strict (hD : D.IsReg) (hT : D.IsTree) (hArc : ArcKilledWordStatement)
    (hq : ∀ (k : ℕ) (t : Fin (k + 1) → ℝ≥0), D.valid (k + 1) t → qLast k (Fin.init t) < qLast (k + 1) t)
    (ω : Ω) (h0 : MarksStrict (D.xL0 ω) (D.xR0 ω)) :
    ∀ (k : ℕ) (t : Fin k → ℝ≥0), ω ∈ D.alive k t →
      MarksStrict (nL₀ := nL₀ + k) (nR₀ := nR₀ + k) (D.marks k t ω).1 (D.marks k t ω).2
  | 0, _, _ => h0
  | k + 1, t, hA => by
    have hγ' := (hD.isKilledFamily k (Fin.init t)).arc ω
    have hA' := hT.alive_init hA hγ'
    obtain ⟨hL0, hLs, hR0, hRs⟩ := TreeData.marks_strict hD hT hArc hq ω h0 k (Fin.init t) hA'
    obtain ⟨⟨hv, hG⟩, hqP⟩ := hA
    have hsum := TreeData.startCap_succ hD hT ⟨⟨hv, hG⟩, hqP⟩ hA'
    set s := candInv D.cand k (Fin.init t) (t (Fin.last k)) ω with hs
    have hsum' : D.startCap k (Fin.init t) ω + s = D.startCap (k + 1) t ω := hsum
    have hQ : qLast (k + 1) t ∈ D.pre k (Fin.init t) ω := (hT.mem_pre_iff hv hG le_rfl).1 hqP
    have hcap : capClock (D.img (k + 1) t ω) (qLast (k + 1) t) =
        capClock (D.img k (Fin.init t) ω) (qLast (k + 1) t) := Prop59Pieces.capClock_congr (hT.img_eqOn hv hG)
    have hlife : ((D.startCap k (Fin.init t) ω + s : ℝ≥0) : WithTop ℝ≥0) <
        kLife (D.img k (Fin.init t) ω) (D.pre k (Fin.init t) ω) := by
      rw [hsum', TreeData.startCap_eq ⟨⟨hv, hG⟩, hqP⟩, hcap]
      exact hγ'.lt_kLife hQ
    have hspos : 0 < s := by
      have h1 : capClock (D.img k (Fin.init t) ω) (qLast k (Fin.init t)) <
          capClock (D.img k (Fin.init t) ω) (qLast (k + 1) t) :=
        hγ'.strictMonoOn_capClock hA'.2 hQ (hq k t hv)
      have h2 : D.startCap k (Fin.init t) ω < D.startCap (k + 1) t ω := by
        rw [TreeData.startCap_eq hA', TreeData.startCap_eq ⟨⟨hv, hG⟩, hqP⟩, hcap]
        exact (Real.toNNReal_lt_toNNReal_iff_of_nonneg (hγ'.capClock_nonneg hA'.2)).2 h1
      rcases eq_zero_or_pos s with h | h
      · rw [h, add_zero] at hsum'
        exact absurd hsum' h2.ne
      · exact h
    have hslt : (s : ℝ≥0∞) < arcζ (fun _ : Unit => D.img k (Fin.init t) ω) (fun _ => D.pre k (Fin.init t) ω)
        (fun _ => D.startCap k (Fin.init t) ω) univ () := by
      rw [← arcζ_onePt hA']
      exact lt_arcζ_iff.2 ⟨hA', hlife⟩
    have hK := hArc (Ω := Unit) (γ := fun _ => D.img k (Fin.init t) ω) (P := fun _ => D.pre k (Fin.init t) ω)
      (S₀ := fun _ => D.startCap k (Fin.init t) ω) (fun _ => hγ') (xL := fun _ => (D.marks k (Fin.init t) ω).1)
      (xR := fun _ => (D.marks k (Fin.init t) ω).2) (fun _ => hL0) (fun _ => hR0) (fun _ => hLs.antitone)
      (fun _ => hRs.monotone)
    have hsepL : ∀ i, (D.cand k (Fin.init t)).VL i s ω < (D.cand k (Fin.init t)).W s ω := fun i => by
      have h := hK.sepL () s hspos hslt i
      show arcVL _ _ _ _ (fun ω => (D.marks k (Fin.init t) ω).1) i s ω < arcW _ _ _ _ s ω
      rw [arcVL_onePt hA', arcW_onePt hA']
      exact h
    have hsepR : ∀ j, (D.cand k (Fin.init t)).W s ω < (D.cand k (Fin.init t)).VR j s ω := fun j => by
      have h := hK.sepR () s hspos hslt j
      show arcW _ _ _ _ s ω < arcVR _ _ _ _ (fun ω => (D.marks k (Fin.init t) ω).2) j s ω
      rw [arcVR_onePt hA', arcW_onePt hA']
      exact h
    rw [TreeData.marks_succ, ← hs]
    refine ⟨fun i => ?_, strictAnti_cons (fun i i' hii => ?_) fun i => ?_, fun j => ?_,
      strictMono_cons (fun j j' hjj => ?_) fun j => ?_⟩
    · refine Fin.cases le_rfl (fun i₀ => ?_) i
      simp only [Fin.cons_succ]
      linarith [hsepL i₀]
    · have h := arcVL_lt_arcVL (A := D.alive k (Fin.init t)) (S₀ := D.startCap k (Fin.init t))
        (xL := fun ω => (D.marks k (Fin.init t) ω).1) hγ' hA' (hLs hii) (hL0 i) hlife
      show _ - _ < _ - _
      exact sub_lt_sub_right h _
    · linarith [hsepL i]
    · refine Fin.cases le_rfl (fun j₀ => ?_) j
      simp only [Fin.cons_succ]
      linarith [hsepR j₀]
    · have h := arcVR_lt_arcVR (A := D.alive k (Fin.init t)) (S₀ := D.startCap k (Fin.init t))
        (xR := fun ω => (D.marks k (Fin.init t) ω).2) hγ' hA' (hRs hjj) (hR0 j) hlife
      show _ - _ < _ - _
      exact sub_lt_sub_right h _
    · linarith [hsepR j]

end Tree

end InteractingSLE.Sec5.CrossCond.StagedNode
