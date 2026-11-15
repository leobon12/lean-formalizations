/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1EightSeedAssembly
import InteractingSLE.Spec.ZhanGT4.DualSeedFusedReciprocity
import InteractingSLE.Spec.ZhanGT4.DualSeedAccessAxis
import InteractingSLE.Spec.ZhanGT4.DualTwoDirEncl

/-!
# Zhan's A.1 (Eight): the two views of one seeded rectangle

Packet PROVE-A1-EIGHTFIN. Source: Astra, *Follow-up proofs*, §A.1.1–A.1.2 and (D6) (`ig1_followup_proofs.txt`
L190–L296: "the normalised density is the same in both views") and follow-up 4 §2.5 (L739–L788).

One protected rectangle of the Eight configuration: the small curve (driver `W₁`, from `0`, its two seeds `Vlo`,
`Vhi`) up to its own horizon `S`, and the large curve (path `V₂`, from `p`) up to `Y`. The seeded records of the
column view are A1-EIGHTSEED's `srcRec W₁ S V₂ t …` (curve `2` frozen at height `t`). The opposite view (curve `2`
grows, curve `1` frozen at own time `a`) is `eView`: A22's `FrzData` whose marks are the **boundary accesses** of the
two seeds of the frozen small hull, `V m a − p`.

This file sets up both views from the enclosures alone, through A15's single-rectangle two-curve enclosure
`TwoEncl` (index type `Unit`, no ordinary marks):

* `stairH_unit`, `imgChain_eq_imgSelD`, `srcRec_eq_sSel`: the records' image data are the canonical selections of
  `TwoEncl` (the staircase width of one rectangle is its column end);
* `srcRec_congr_frozen`: a record only reads the frozen path up to its height (used for A1-EIGHTSEED's stopped
  frozen paths);
* `ViewSetup` (the enclosure and seed hypotheses of one rectangle) and its consequences: the `TwoEncl` instance, the
  column view at every height (`ViewSetup.sOwn`, the frozen tip alive), the opposite view at every own time
  (`ViewSetup.tOwn`, the frozen small tip alive), and the two-view rectangle (`ViewSetup.twoViewRect`);
* `eView`, the opposite-view data with the seed accesses as marks.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric

namespace InteractingSLE.ZhanGT4.A1EightFin

open QuantumZipper (H IsForwardSol fwdMap fwdHull)
open A1SeedField A1EightSeed

/-! ### One rectangle: the staircase width and the canonical selections -/

section Select

/-- The staircase width of a single rectangle `[0, S] × [0, Y]` at a height `v ≤ Y` is the column end `S`. -/
theorem stairH_unit {S Y v : ℝ} (hS : 0 ≤ S) (hv : v ≤ Y) :
    stairH (fun _ : Unit => Y) (fun _ : Unit => S) v = S := by
  apply le_antisymm
  · unfold stairH
    refine Finset.max'_le _ _ _ fun z hz => ?_
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact hS
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
      exact le_rfl
  · exact le_stairH (S₁ := fun _ : Unit => Y) (S₂ := fun _ : Unit => S) (i := ()) hv

/-- A1-EIGHTSEED's image-data choice is A15's deterministic selection. -/
theorem imgChain_eq_imgSelD (W V : ℝ → ℝ) (w y : ℝ) :
    imgChain W (fwdHull V y) (frzChart V y) w = imgSelD W V w y := by
  unfold imgChain imgSelD
  split_ifs <;> rfl

variable {n : ℕ}

/-- **The column records are the canonical `s`-view of one rectangle.** -/
theorem srcRec_eq_sSel (W₁ V₂ : ℝ → ℝ) {S Y t : ℝ} (hS : 0 ≤ S) (ht : t ≤ Y) (κ : ℝ) (rr : Fin n → ℝ) (p : ℝ)
    (V : Fin n → ℝ → ℝ) :
    srcRec W₁ S V₂ t κ rr p V = SeedData.fromSource W₁ (sSelW W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) t)
      (sSelA W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) t) (frzChart V₂ t) κ rr (V₂ t) p V := by
  simp only [srcRec, sSelW, sSelA, stairH_unit hS ht, imgChain_eq_imgSelD]

/-- **A record reads the frozen path only up to its height**: two frozen paths, continuous on `[0, t']` with `t < t'`
and equal on `[0, t]`, give the same record at height `t`. -/
theorem srcRec_congr_frozen {W Wf Wf' : ℝ → ℝ} {T t t' κ p : ℝ} {rr : Fin n → ℝ} {V : Fin n → ℝ → ℝ}
    (hc : ContinuousOn Wf (Icc 0 t')) (hc' : ContinuousOn Wf' (Icc 0 t')) (ht : 0 ≤ t) (htt : t < t')
    (h : EqOn Wf Wf' (Icc 0 t)) : srcRec W T Wf t κ rr p V = srcRec W T Wf' t κ rr p V := by
  have hK : fwdHull Wf t = fwdHull Wf' t := LocalExt.fwdHull_congr_of_continuousOn hc hc' ht htt h
  have hφ : frzChart Wf t = frzChart Wf' t := by
    funext z
    simp only [frzChart, Ito.fwdMap_congr_of_eqOn h, h ⟨ht, le_rfl⟩]
  have hv : Wf t = Wf' t := h ⟨ht, le_rfl⟩
  simp only [srcRec, hK, hφ, hv]

end Select

/-! ### The enclosure data of one rectangle -/

/-- **The enclosure and seed hypotheses of one protected rectangle**: the protected pair, the small curve's continuous
driver `W₁` (from `0`) up to `0 < S ≤ Tm` with hull in `H₁`, the large curve's continuous path `V₂` (from `p`) up to
`0 < Y ≤ Tm` with hull in `H₂`, and the two seeds `Vlo`, `Vhi` of the small curve (seed coordinates of `W₁`, the
driver between them, distinct at positive times). -/
structure ViewSetup (H₁ H₂ : Set ℂ) (δ p q dd Tm : ℝ) (W₁ V₂ : ℝ → ℝ) (S Y : ℝ) (Vlo Vhi : ℝ → ℝ) : Prop where
  pp : IsProtectedPair H₁ H₂ δ p q dd
  cont₁ : Continuous W₁
  zero₁ : W₁ 0 = 0
  pos₁ : 0 < S
  le₁ : S ≤ Tm
  K₁ : fwdHull W₁ S ⊆ H₁
  cont₂ : Continuous V₂
  zero₂ : V₂ 0 = p
  pos₂ : 0 < Y
  le₂ : Y ≤ Tm
  K₂ : fwdHull V₂ Y ⊆ H₂
  lo : IsSeedCoordinate W₁ Vlo S
  hi : IsSeedCoordinate W₁ Vhi S
  drv : ∀ t ∈ Icc (0 : ℝ) S, W₁ t ∈ uIcc (Vlo t) (Vhi t)
  inj : ∀ t ∈ Ioc (0 : ℝ) S, Vlo t ≠ Vhi t

namespace ViewSetup

variable {H₁ H₂ : Set ℂ} {δ p q dd Tm : ℝ} {W₁ V₂ : ℝ → ℝ} {S Y : ℝ} {Vlo Vhi : ℝ → ℝ}
  (h : ViewSetup H₁ H₂ δ p q dd Tm W₁ V₂ S Y Vlo Vhi)
include h

/-- The single-rectangle two-curve enclosure (A15's `TwoEncl`, no ordinary marks). -/
theorem twoEncl :
    TwoEncl W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) (fun _ => H₁) (fun _ => H₂) (fun _ => δ) (fun _ => q)
      (fun _ => dd) (Fin.elim0 : Fin 0 → ℝ) Tm where
  cont₁ := h.cont₁
  cont₂ := h.cont₂
  zero₁ := h.zero₁
  hull₁ := fun _ => h.pp.hull₁
  hull₂ := fun _ => h.pp.hull₂
  δpos := fun _ => h.pp.sep_pos
  sep := fun _ => h.pp.sep
  dpos := fun _ => h.pp.rad_pos
  qpos := fun _ => h.pp.prot_pos
  qH := fun _ => h.pp.prot
  pH := fun _ m => Fin.elim0 m
  pinj := fun m => Fin.elim0 m
  start₂ := fun _ => by rw [h.zero₂]; exact h.pp.src
  qW := fun _ => by rw [h.zero₂]; exact h.pp.prot_lt
  S₁pos := fun _ => h.pos₁
  S₂pos := fun _ => h.pos₂
  S₁le := fun _ => h.le₁
  S₂le := fun _ => h.le₂
  K₁ := fun _ => h.K₁
  K₂ := fun _ => h.K₂

/-- **The column view at every height `t ≤ Y`**: the canonical image data up to the horizon `S`, with the frozen tip
`V₂ t` alive for the image chain. -/
theorem sOwn {t : ℝ} (ht : t ∈ Icc (0 : ℝ) Y) :
    OwnData W₁ (fwdHull V₂ t) (frzChart V₂ t) S (sSelA W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) t)
        (sSelW W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) t) ∧
      ∃ v, IsForwardSol (sSelW W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) t) ((V₂ t : ℝ) : ℂ)
        (sSelA W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) t S) v := by
  obtain ⟨-, hown, htip, -⟩ := h.twoEncl.sView_encl () ht
  rw [stairH_unit h.pos₁.le ht.2] at hown htip
  exact ⟨hown, htip⟩

/-- **The opposite view at every own time `u ≤ S`** (coordinates translated by `−p`): the canonical image data up to
the horizon `Y`, with the frozen small tip `W₁ u − p` alive for the image chain. -/
theorem tOwn {u : ℝ} (hu : u ∈ Icc (0 : ℝ) S) :
    OwnData (fun s => V₂ s - V₂ 0) (fwdHull (fun s => W₁ s - V₂ 0) u) (frzChart (fun s => W₁ s - V₂ 0) u) Y
        (tSelA W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) u)
        (tSelW W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) u) ∧
      ∃ v, IsForwardSol (tSelW W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) u) ((W₁ u - V₂ 0 : ℝ) : ℂ)
        (tSelA W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) u Y) v := by
  obtain ⟨-, hown, htip, -⟩ := h.twoEncl.tView_encl () hu
  rw [stairH_unit h.pos₂.le hu.2] at hown htip
  exact ⟨hown, htip⟩

/-- **The two-view rectangle** of the canonical selections. -/
theorem twoViewRect :
    TwoViewRect W₁ V₂ S Y (sSelA W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y))
      (sSelW W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y)) (tSelA W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y))
      (tSelW W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y)) :=
  h.twoEncl.twoViewRect ()

end ViewSetup

/-! ### The opposite view with the seed accesses as marks -/

/-- **The opposite view at own time `a`** (curve `2` grows from `0` after translating by `−V₂ 0`, curve `1` frozen at
`a`): A15's canonical `t`-view image data, the dual parameter `16/κ`, the dual charges `−(κ/4) r_m`, the frozen small
tip `W₁ a − V₂ 0`, and as marks the boundary accesses `V m a − V₂ 0` of the small curve's seeds. -/
def eView {n : ℕ} (κ : ℝ) (rr : Fin n → ℝ) (W₁ V₂ : ℝ → ℝ) (S Y : ℝ) (V : Fin n → ℝ → ℝ) (a : ℝ) : FrzData n :=
  ⟨fun u => V₂ u - V₂ 0, tSelW W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) a,
    tSelA W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) a, frzChart (fun u => W₁ u - V₂ 0) a, 16 / κ,
    fun m => -(κ / 4) * rr m, W₁ a - V₂ 0, fun m => V m a - V₂ 0⟩

end InteractingSLE.ZhanGT4.A1EightFin
