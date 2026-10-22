import HigherDimLQGMetric.DGZ.CoverGeometry
import HigherDimLQGMetric.DGZ.Sec41Lemma41

/-!
# One-centre-at-a-time selection for DGZ Proposition 5.10

At level `i + 1`, an entry records a bad fine box, its chosen containing coarse box, and the
certificate supplied by the nice coarse box.  A finite induction over bad fine boxes inserts a
new entry only when the box is not already covered.  The interior-face margin of the parent
choice makes the selected centres separated.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric.DGZ

open Set HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt cbox obox)

variable {d : ℕ}

/-- One selected centre at fine level `i+1`, with its parent and its bad-box witness. -/
structure CoverEntry (p : NiceParams) (H : ℕ → Rd d → ℝ) (i : ℕ) where
  y : Zd d
  u : Zd d
  z : Zd d
  bad : ¬ NiceBox p H (i + 1) y
  small : obox (latPt (p.s (i + 1)) y) (p.s (i + 1)) ⊆ obox (0 : Rd d) 2
  parent : obox (latPt (p.s (i + 1)) y) (p.s (i + 1)) ⊆
    obox (latPt (p.s (i + 2)) u) (p.s (i + 2))
  big : obox (latPt (p.s (i + 2)) u) (p.s (i + 2)) ⊆ obox (0 : Rd d) 2
  margin : ∀ y' : Zd d,
    obox (latPt (p.s (i + 1)) y') (p.s (i + 1)) ⊆ obox (0 : Rd d) 2 →
    ¬ obox (latPt (p.s (i + 1)) y') (p.s (i + 1)) ⊆
      obox (latPt (p.s (i + 2)) u) (p.s (i + 2)) →
    ∃ k : Fin d, ((2 ^ (p.a (i + 2) - p.a (i + 1)) : ℕ) : ℤ) ≤ 2 * |y k - y' k|
  zmem : latPt (p.s (i + 1)) z ∈ obox (latPt (p.s (i + 2)) u) (p.s (i + 2))
  covers : ∀ v : Zd d,
    obox (latPt (p.s (i + 1)) v) (p.s (i + 1)) ⊆
      obox (latPt (p.s (i + 2)) u) (p.s (i + 2)) →
    ¬ NiceBox p H (i + 1) v →
    obox (latPt (p.s (i + 1)) v) (p.s (i + 1)) ⊆
      obox (latPt (p.s (i + 1)) z) (p.R * p.s (i + 1))
  cert : NiceCEvent p H (i + 2) u z

/-- A bad fine box whose parent is nice gives one entry. -/
theorem coverEntry_of_bad (p : NiceParams) (H : ℕ → Rd d → ℝ)
    (hmono : Monotone p.a) {i : ℕ} (hjn : p.a (i + 2) ≤ p.n)
    (y : Zd d) (hy : obox (latPt (p.s (i + 1)) y) (p.s (i + 1)) ⊆ obox (0 : Rd d) 2)
    (hbad : ¬ NiceBox p H (i + 1) y)
    (hnice : ∀ u : Zd d,
      obox (latPt (p.s (i + 2)) u) (p.s (i + 2)) ⊆ obox (0 : Rd d) 2 →
      obox (latPt (p.s (i + 1)) y) (p.s (i + 1)) ⊆
        obox (latPt (p.s (i + 2)) u) (p.s (i + 2)) → NiceBox p H (i + 2) u) :
    ∃ e : CoverEntry p H i, e.y = y := by
  obtain ⟨u, hparent, hbig, hmargin⟩ := exists_niceParent p hmono hjn y hy
  obtain ⟨_, hbranch⟩ := (niceBox_add_two_iff p H i u).mp (hnice u hbig hparent)
  rcases hbranch with hall | ⟨z, hz, hcov, hC⟩
  · exact False.elim (hbad (hall y hparent))
  · exact ⟨⟨y, u, z, hbad, hy, hparent, hbig, hmargin, hz, hcov, hC⟩, rfl⟩

/-- The chosen `R`-box covers its own bad witness. -/
theorem CoverEntry.self_cover {p : NiceParams} {H : ℕ → Rd d → ℝ} {i : ℕ}
    (e : CoverEntry p H i) :
    obox (latPt (p.s (i + 1)) e.y) (p.s (i + 1)) ⊆
      obox (latPt (p.s (i + 1)) e.z) (p.R * p.s (i + 1)) :=
  e.covers e.y e.parent e.bad

/-- A new bad box left uncovered by an old entry gives a separated new centre. -/
theorem coverEntry_sep_of_uncovered (p : NiceParams) (H : ℕ → Rd d → ℝ)
    (hmono : Monotone p.a) {i : ℕ} (hjn : p.a (i + 2) ≤ p.n)
    (hR : 1 ≤ p.R)
    (hgap : 40 * (p.R : ℝ) * p.s (i + 1) ≤ p.s (i + 2))
    (e e' : CoverEntry p H i)
    (hnot : ¬ obox (latPt (p.s (i + 1)) e'.y) (p.s (i + 1)) ⊆
      obox (latPt (p.s (i + 1)) e.z) (p.R * p.s (i + 1))) :
    latPt (p.s (i + 1)) e'.z ∉
      cbox (latPt (p.s (i + 1)) e.z) (p.s (i + 2) / 4) := by
  let N := 2 ^ (p.a (i + 2) - p.a (i + 1))
  have heq : (N : ℝ) * p.s (i + 1) = p.s (i + 2) := by
    rw [p.s_succ_eq (hmono (Nat.le_succ (i + 1))) hjn]
    simp only [N, Nat.cast_pow, Nat.cast_ofNat]
  have hgapN : (40 : ℝ) * p.R ≤ N := by
    apply le_of_mul_le_mul_right (a0 := p.s_pos (i + 1))
    calc (40 * (p.R : ℝ)) * p.s (i + 1) =
          40 * (p.R : ℝ) * p.s (i + 1) := by ring
      _ ≤ p.s (i + 2) := hgap
      _ = (N : ℝ) * p.s (i + 1) := heq.symm
  have hnotParent : ¬ obox (latPt (p.s (i + 1)) e'.y) (p.s (i + 1)) ⊆
      obox (latPt (p.s (i + 2)) e.u) (p.s (i + 2)) := by
    intro h
    exact hnot (e.covers e'.y h e'.bad)
  have hm := e.margin e'.y e'.small hnotParent
  have hz := cover_fine_close (p.s_pos (i + 1)) e.self_cover
  have hz' := cover_fine_close (p.s_pos (i + 1)) e'.self_cover
  have h := cover_sep_of_margin (p.s_pos (i + 1)) hR hgapN hm hz hz'
  simpa only [heq] using h

/-- Pairwise separation of the selected centres at a fixed level. -/
def CoverEntriesSeparated (p : NiceParams) (H : ℕ → Rd d → ℝ) (i : ℕ)
    (S : Finset (CoverEntry p H i)) : Prop :=
  ∀ e ∈ S, ∀ e' ∈ S, e ≠ e' →
    latPt (p.s (i + 1)) e'.z ∉
      cbox (latPt (p.s (i + 1)) e.z) (p.s (i + 2) / 4)

/-- Greedy selection from a finite collection of bad boxes.  A candidate is processed only if
none of the already chosen `R`-boxes contains it. -/
theorem exists_coverEntries_finset (p : NiceParams) (H : ℕ → Rd d → ℝ)
    (hmono : Monotone p.a) {i : ℕ} (hjn : p.a (i + 2) ≤ p.n)
    (hR : 1 ≤ p.R)
    (hgap : 40 * (p.R : ℝ) * p.s (i + 1) ≤ p.s (i + 2))
    (Uhi : Set (Rd d))
    (hnice : ∀ u : Zd d,
      obox (latPt (p.s (i + 2)) u) (p.s (i + 2)) ⊆ obox (0 : Rd d) 2 →
      ¬ obox (latPt (p.s (i + 2)) u) (p.s (i + 2)) ⊆ Uhi → NiceBox p H (i + 2) u)
    (F : Finset (Zd d)) :
    (∀ y ∈ F, ¬ NiceBox p H (i + 1) y ∧
      obox (latPt (p.s (i + 1)) y) (p.s (i + 1)) ⊆ obox (0 : Rd d) 2 ∧
      ¬ obox (latPt (p.s (i + 1)) y) (p.s (i + 1)) ⊆ Uhi) →
    ∃ S : Finset (CoverEntry p H i), CoverEntriesSeparated p H i S ∧
      (∀ y ∈ F, ∃ e ∈ S,
        obox (latPt (p.s (i + 1)) y) (p.s (i + 1)) ⊆
          obox (latPt (p.s (i + 1)) e.z) (p.R * p.s (i + 1))) ∧
      ∀ e ∈ S, ¬ obox (latPt (p.s (i + 1)) e.y) (p.s (i + 1)) ⊆ Uhi := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    intro _
    refine ⟨∅, ?_, ?_, ?_⟩
    · intro e he
      simp at he
    · intro y hy
      simp at hy
    · intro e he
      simp at he
  | @insert y F hyF ih =>
    intro hF
    have hF' : ∀ v ∈ F, ¬ NiceBox p H (i + 1) v ∧
        obox (latPt (p.s (i + 1)) v) (p.s (i + 1)) ⊆ obox (0 : Rd d) 2 ∧
        ¬ obox (latPt (p.s (i + 1)) v) (p.s (i + 1)) ⊆ Uhi := by
      intro v hv
      exact hF v (Finset.mem_insert_of_mem hv)
    obtain ⟨S, hsep, hcov, hout⟩ := ih hF'
    obtain ⟨hbad, hsmall, hU⟩ := hF y (Finset.mem_insert_self y F)
    by_cases hcovered : ∃ e ∈ S,
        obox (latPt (p.s (i + 1)) y) (p.s (i + 1)) ⊆
          obox (latPt (p.s (i + 1)) e.z) (p.R * p.s (i + 1))
    · refine ⟨S, hsep, ?_, hout⟩
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact hcovered
      · exact hcov v hv
    · have hnice' (u : Zd d)
          (hbig : obox (latPt (p.s (i + 2)) u) (p.s (i + 2)) ⊆ obox (0 : Rd d) 2)
          (hparent : obox (latPt (p.s (i + 1)) y) (p.s (i + 1)) ⊆
            obox (latPt (p.s (i + 2)) u) (p.s (i + 2))) : NiceBox p H (i + 2) u := by
          apply hnice u hbig
          intro hbigU
          exact hU (hparent.trans hbigU)
      obtain ⟨e, hey⟩ := coverEntry_of_bad p H hmono hjn y hsmall hbad hnice'
      have heSelf : obox (latPt (p.s (i + 1)) y) (p.s (i + 1)) ⊆
          obox (latPt (p.s (i + 1)) e.z) (p.R * p.s (i + 1)) := by
        rw [← hey]
        exact e.self_cover
      have heS : e ∉ S := by
        intro heS
        exact hcovered ⟨e, heS, heSelf⟩
      refine ⟨insert e S, ?_, ?_, ?_⟩
      · intro e₀ he₀ e₁ he₁ hne
        rcases Finset.mem_insert.mp he₀ with heq₀ | he₀
        · subst e₀
          rcases Finset.mem_insert.mp he₁ with heq₁ | he₁
          · subst e₁
            exact False.elim (hne rfl)
          · have hnot : ¬ obox (latPt (p.s (i + 1)) e.y) (p.s (i + 1)) ⊆
                obox (latPt (p.s (i + 1)) e₁.z) (p.R * p.s (i + 1)) := by
              rw [hey]
              intro h
              exact hcovered ⟨e₁, he₁, h⟩
            have hsep' := coverEntry_sep_of_uncovered p H hmono hjn hR hgap e₁ e hnot
            intro hc
            apply hsep'
            intro k
            simpa only [abs_sub_comm] using hc k
        · rcases Finset.mem_insert.mp he₁ with heq₁ | he₁
          · subst e₁
            have hnot : ¬ obox (latPt (p.s (i + 1)) e.y) (p.s (i + 1)) ⊆
                obox (latPt (p.s (i + 1)) e₀.z) (p.R * p.s (i + 1)) := by
              rw [hey]
              intro h
              exact hcovered ⟨e₀, he₀, h⟩
            exact coverEntry_sep_of_uncovered p H hmono hjn hR hgap e₀ e hnot
          · exact hsep e₀ he₀ e₁ he₁ hne
      · intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact ⟨e, Finset.mem_insert_self _ _, heSelf⟩
        · obtain ⟨e₀, he₀, hc₀⟩ := hcov v hv
          exact ⟨e₀, Finset.mem_insert_of_mem he₀, hc₀⟩
      · intro v hv
        rcases Finset.mem_insert.mp hv with heq | hv
        · subst v
          rw [hey]
          exact hU
        · exact hout v hv

/-- Only finitely many lattice boxes of one scale are contained in `B₂(0)`. -/
theorem finite_niceBoxes_in_two (p : NiceParams) (j : ℕ) :
    ({y : Zd d | obox (latPt (p.s j) y) (p.s j) ⊆ obox (0 : Rd d) 2} : Set (Zd d)).Finite := by
  let M := 2 ^ (p.n - p.a j + 1)
  have hsM : p.s j * M = 2 := p.s_mul_two_pow j
  apply finite_of_forall_withinInf (R' := (M : ℤ) - 1)
  intro y hy
  change obox (latPt (p.s j) y) (p.s j) ⊆ obox (0 : Rd d) 2 at hy
  have h : obox (latPt (p.s j) y) (p.s j) ⊆
      obox (latPt (p.s j) (0 : Zd d)) (p.s j * M) := by
    simpa only [hsM, HigherDimLFPP.DGZ.latPt_zero] using hy
  exact (obox_latPt_subset_iff (p.s_pos j)).mp h

/-- The finite greedy selection covers every bad fine box still outside the higher-level cover. -/
theorem exists_coverEntries_level (p : NiceParams) (H : ℕ → Rd d → ℝ)
    (hmono : Monotone p.a) {i : ℕ} (hjn : p.a (i + 2) ≤ p.n)
    (hR : 1 ≤ p.R)
    (hgap : 40 * (p.R : ℝ) * p.s (i + 1) ≤ p.s (i + 2))
    (Uhi : Set (Rd d))
    (hnice : ∀ u : Zd d,
      obox (latPt (p.s (i + 2)) u) (p.s (i + 2)) ⊆ obox (0 : Rd d) 2 →
      ¬ obox (latPt (p.s (i + 2)) u) (p.s (i + 2)) ⊆ Uhi → NiceBox p H (i + 2) u) :
    ∃ S : Finset (CoverEntry p H i), CoverEntriesSeparated p H i S ∧
      (∀ y : Zd d, ¬ NiceBox p H (i + 1) y →
        obox (latPt (p.s (i + 1)) y) (p.s (i + 1)) ⊆ obox (0 : Rd d) 2 →
        ¬ obox (latPt (p.s (i + 1)) y) (p.s (i + 1)) ⊆ Uhi →
        ∃ e ∈ S,
          obox (latPt (p.s (i + 1)) y) (p.s (i + 1)) ⊆
            obox (latPt (p.s (i + 1)) e.z) (p.R * p.s (i + 1))) ∧
      ∀ e ∈ S, ¬ obox (latPt (p.s (i + 1)) e.y) (p.s (i + 1)) ⊆ Uhi := by
  classical
  let F : Set (Zd d) := {y | ¬ NiceBox p H (i + 1) y ∧
    obox (latPt (p.s (i + 1)) y) (p.s (i + 1)) ⊆ obox (0 : Rd d) 2 ∧
    ¬ obox (latPt (p.s (i + 1)) y) (p.s (i + 1)) ⊆ Uhi}
  have hF : F.Finite :=
    (finite_niceBoxes_in_two p (i + 1)).subset (fun y hy => hy.2.1)
  obtain ⟨S, hsep, hcov, hout⟩ := exists_coverEntries_finset p H hmono hjn hR hgap Uhi hnice
    hF.toFinset (by
      intro y hy
      exact hF.mem_toFinset.mp hy)
  refine ⟨S, hsep, ?_, hout⟩
  intro y hbad hsmall hnot
  exact hcov y (hF.mem_toFinset.mpr ⟨hbad, hsmall, hnot⟩)

end HigherDimLQGMetric.DGZ
