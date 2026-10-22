import HigherDimLQGMetric.DGZ.FoldDefs
import HigherDimLFPP.Perc.Lattice

/-!
# Lattice connectivity of a thick shell inside a box (packet L3a2, MA7 D-SHELL)

Source: Ding–Gwynne–Zhuang, arXiv:2310.03996v5 ([2]), Lemma 4.9, around half (TeX l. 1898); planning
audit `planning/audits/MA7-ref2-sections-4-6.md`, gap G3 and Details (a) D-SHELL (used in step (4)
of D-4.9: the reference path for box surgery joins the two free sites inside the shell).

Main results (namespace `HigherDimLQGMetric.DGZ`):

* `shellLatticeConn` (MA7 D-SHELL): for `d ≥ 2`, `c ∈ Λ = latBox a b`, integers `1 ≤ ρ₂ < ρ₁` and
  `cᵢ + ρ₁ ≤ bᵢ` or `aᵢ ≤ cᵢ - ρ₁` for every `i`, the shell
  `M = {x ∈ Λ : ρ₂ ≤ |x - c|_∞ ≤ ρ₁}` is L-connected;
* `exists_shell_chain`: the same, as an L-chain (`List`) between two sites of `M`, the form
  consumed by `BoxSurgery`;
* `connIn_latBox`: lattice boxes are L-connected; `reflTransGen_of_forall_between`: two sites are
  joined by an L-path inside any set containing every site whose coordinates lie between theirs;
  `withinInf_iff_mem_latBox`: `B̄_r(c) ∩ ℤ^d = latBox (c - r) (c + r)`.

Proof of D-SHELL (MA7, with hubs). Choose for every `j` a value `τⱼ = cⱼ ± ρ₂ ∈ [aⱼ, bⱼ]` (the sign
given by the hypothesis on the side `cⱼ ± ρ₁`) and the hub `qⱼ = c + (τⱼ - cⱼ) eⱼ`. Two sites of
`Λ ∩ B̄_{ρ₁}(c)` lying in a common *slab* (`xᵢ, yᵢ ≥ cᵢ + ρ₂` or `xᵢ, yᵢ ≤ cᵢ - ρ₂` for some `i`)
are joined inside `M`, since all sites of their bounding box lie in the same slab
(`reflTransGen_shell_of_slab`). A site `x ∈ M` with `|xᵢ - cᵢ| ≥ ρ₂` is joined to the hub `qⱼ`
(`j ≠ i`, which exists since `d ≥ 2`) through `p = qⱼ + (α - cᵢ) eᵢ`, `α = cᵢ ± ρ₂` on the side of
`xᵢ` (`x, p` share the slab of `i`, `p, qⱼ` that of `j`); two hubs `qⱼ, qⱼ'` are joined through
`qⱼ + (τⱼ' - cⱼ') eⱼ'`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HigherDimLQGMetric

namespace DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open Relation

variable {d : ℕ}

/-! ### Bounding boxes and lattice boxes -/

/-- **Bounding-box paths.** If `S` contains every site whose coordinates lie between those of `x`
and `y`, then `x` and `y` are joined by an L-path in `S` (change one coordinate at a time). -/
lemma reflTransGen_of_forall_between {S : Set (Zd d)} {x y : Zd d}
    (h : ∀ z : Zd d, (∀ k, min (x k) (y k) ≤ z k ∧ z k ≤ max (x k) (y k)) → z ∈ S) :
    ReflTransGen (StepIn S LAdj) x y := by
  have key : ∀ n : ℕ, ReflTransGen (StepIn S LAdj) x (coordPath x y n) := by
    intro n
    induction n with
    | zero => rw [coordPath_zero]
    | succ n ih =>
      by_cases hn : n < d
      · have hupd : coordPath x y (n + 1) =
            Function.update (coordPath x y n) ⟨n, hn⟩ (y ⟨n, hn⟩) := by
          funext k
          by_cases hk : k = ⟨n, hn⟩
          · subst hk
            simp [coordPath]
          · rw [Function.update_of_ne hk]
            have hkn : k.val ≠ n := fun h => hk (Fin.ext h)
            have e : (k.val < n + 1) ↔ (k.val < n) := by omega
            simp only [coordPath, e]
        have hxn : coordPath x y n ⟨n, hn⟩ = x ⟨n, hn⟩ := by simp [coordPath]
        rw [hupd]
        refine ih.trans (reflTransGen_update _ _ _ fun t ht1 ht2 => h _ fun k => ?_)
        rw [hxn] at ht1 ht2
        by_cases hk : k = ⟨n, hn⟩
        · subst hk
          rw [Function.update_self]
          omega
        · rw [Function.update_of_ne hk]
          simp only [coordPath]
          split_ifs <;> omega
      · rw [coordPath_of_le x y (by omega : d ≤ n + 1)]
        rwa [coordPath_of_le x y (by omega : d ≤ n)] at ih
  have h' := key d
  rwa [coordPath_of_le x y le_rfl] at h'

/-- Lattice boxes are L-connected. -/
lemma connIn_latBox (a b : Zd d) : ConnIn (latBox a b) LAdj := by
  intro x hx y hy
  refine reflTransGen_of_forall_between fun z hz k => ?_
  have h1 := hx k
  have h2 := hy k
  have h3 := hz k
  constructor <;> omega

/-- The `ℓ^∞` ball `B̄_r(c) ∩ ℤ^d` is the lattice box `[c - r, c + r]`. -/
lemma withinInf_iff_mem_latBox {r : ℤ} {x c : Zd d} :
    WithinInf r x c ↔ x ∈ latBox (fun i => c i - r) (fun i => c i + r) := by
  show (∀ i, |x i - c i| ≤ r) ↔ ∀ i, c i - r ≤ x i ∧ x i ≤ c i + r
  refine forall_congr' fun i => ?_
  rw [abs_le]
  constructor <;> intro h <;> constructor <;> omega

/-- An L-path in `S` from a site of `S` gives an L-chain (`List`) of sites of `S` with the same
endpoints. -/
lemma exists_lAdj_chain_of_reflTransGen {S : Set (Zd d)} {u v : Zd d} (hu : u ∈ S)
    (h : ReflTransGen (StepIn S LAdj) u v) :
    ∃ γ : List (Zd d), γ.IsChain LAdj ∧ γ.head? = some u ∧ γ.getLast? = some v ∧
      ∀ x ∈ γ, x ∈ S := by
  obtain ⟨l, hl, hlast⟩ := List.exists_isChain_cons_of_relationReflTransGen h
  have hmem : ∀ (w : Zd d) (m : List (Zd d)), (w :: m).IsChain (StepIn S LAdj) → w ∈ S →
      ∀ x ∈ w :: m, x ∈ S := by
    intro w m
    induction m generalizing w with
    | nil =>
      intro _ hw x hx
      rw [List.mem_singleton] at hx
      rw [hx]
      exact hw
    | cons w' m ih =>
      intro hch hw x hx
      rw [List.isChain_cons_cons] at hch
      rcases List.mem_cons.1 hx with hx | hx
      · rw [hx]
        exact hw
      · exact ih w' hch.2 hch.1.2.1 x hx
  refine ⟨u :: l, hl.imp fun _ _ h => h.2.2, rfl, ?_, hmem u l hl hu⟩
  rw [List.getLast?_eq_some_getLast (List.cons_ne_nil u l), hlast]

/-! ### MA7 D-SHELL -/

section Shell

variable {a b c : Zd d} {ρ₁ ρ₂ : ℤ}

/-- **Slabs.** Two sites of `latBox a b ∩ B̄_{ρ₁}(c)` lying on the same side `±(· - cᵢ) ≥ ρ₂` of a
common coordinate `i` are joined by an L-path in the shell `{x ∈ Λ : ρ₂ ≤ |x - c|_∞ ≤ ρ₁}`: every
site of their bounding box lies in the same slab. -/
lemma reflTransGen_shell_of_slab {x y : Zd d} (hx : x ∈ latBox a b) (hxc : WithinInf ρ₁ x c)
    (hy : y ∈ latBox a b) (hyc : WithinInf ρ₁ y c)
    (hside : ∃ i, (c i + ρ₂ ≤ x i ∧ c i + ρ₂ ≤ y i) ∨ (x i + ρ₂ ≤ c i ∧ y i + ρ₂ ≤ c i)) :
    ReflTransGen
      (StepIn {z | z ∈ latBox a b ∧ (∃ i, ρ₂ ≤ |z i - c i|) ∧ WithinInf ρ₁ z c} LAdj) x y := by
  refine reflTransGen_of_forall_between fun z hz => ⟨fun k => ?_, ?_, fun k => ?_⟩
  · have h1 := hx k
    have h2 := hy k
    have h3 := hz k
    constructor <;> omega
  · obtain ⟨i, hi⟩ := hside
    refine ⟨i, ?_⟩
    have h3 := hz i
    rw [le_abs]
    omega
  · have h1 := hxc k
    have h2 := hyc k
    have h3 := hz k
    rw [abs_le] at h1 h2 ⊢
    omega

/-- Updating one coordinate of a site of `latBox a b ∩ B̄_{ρ₁}(c)` by a value in the allowed range
keeps it there. -/
lemma update_mem_latBox_withinInf {z : Zd d} (hz : z ∈ latBox a b) (hzc : WithinInf ρ₁ z c)
    (k : Fin d) {v : ℤ} (hv1 : a k ≤ v) (hv2 : v ≤ b k) (hv3 : |v - c k| ≤ ρ₁) :
    Function.update z k v ∈ latBox a b ∧ WithinInf ρ₁ (Function.update z k v) c := by
  refine ⟨fun m => ?_, fun m => ?_⟩
  · by_cases hm : m = k
    · subst hm
      rw [Function.update_self]
      exact ⟨hv1, hv2⟩
    · rw [Function.update_of_ne hm]
      exact hz m
  · by_cases hm : m = k
    · subst hm
      rw [Function.update_self]
      exact hv3
    · rw [Function.update_of_ne hm]
      exact hzc m

/-- **MA7 D-SHELL: lattice connectivity of a thick shell inside a box.** Let `d ≥ 2`, `c ∈ ℤ^d`,
integers `1 ≤ ρ₂ < ρ₁`, and `Λ = latBox a b ∋ c` such that for every `i`, `cᵢ + ρ₁ ≤ bᵢ` or
`aᵢ ≤ cᵢ - ρ₁`. Then `M = {x ∈ Λ : ρ₂ ≤ |x - c|_∞ ≤ ρ₁}` is L-connected. -/
theorem shellLatticeConn (hd : 2 ≤ d) (hρ₂ : 1 ≤ ρ₂) (hρ : ρ₂ < ρ₁) (hc : c ∈ latBox a b)
    (hside : ∀ i, c i + ρ₁ ≤ b i ∨ a i ≤ c i - ρ₁) :
    ConnIn {x | x ∈ latBox a b ∧ (∃ i, ρ₂ ≤ |x i - c i|) ∧ WithinInf ρ₁ x c} LAdj := by
  set M := {x | x ∈ latBox a b ∧ (∃ i, ρ₂ ≤ |x i - c i|) ∧ WithinInf ρ₁ x c} with hM
  have hcc : WithinInf ρ₁ c c := withinInf_refl (by omega) c
  -- the hub values `τ j = c j ± ρ₂ ∈ [a j, b j]`
  have hτ : ∀ j, ∃ v, a j ≤ v ∧ v ≤ b j ∧ (v = c j + ρ₂ ∨ v = c j - ρ₂) := fun j => by
    have hcj := hc j
    rcases hside j with h | h
    · exact ⟨c j + ρ₂, by omega, by omega, Or.inl rfl⟩
    · exact ⟨c j - ρ₂, by omega, by omega, Or.inr rfl⟩
  choose τ hτ1 hτ2 hτ3 using hτ
  have hτc : ∀ j, |τ j - c j| ≤ ρ₁ := fun j => by
    rw [abs_le]
    rcases hτ3 j with h | h <;> constructor <;> omega
  -- the hubs `q j = c + (τ j - c j) e_j`
  have hq : ∀ j, Function.update c j (τ j) ∈ latBox a b ∧
      WithinInf ρ₁ (Function.update c j (τ j)) c := fun j =>
    update_mem_latBox_withinInf hc hcc j (hτ1 j) (hτ2 j) (hτc j)
  -- the side of `τ j` at the hub coordinate, for any site with that coordinate equal to `τ j`
  have hτside : ∀ j (x y : Zd d), x j = τ j → y j = τ j →
      (c j + ρ₂ ≤ x j ∧ c j + ρ₂ ≤ y j) ∨ (x j + ρ₂ ≤ c j ∧ y j + ρ₂ ≤ c j) := by
    intro j x y hx hy
    rw [hx, hy]
    rcases hτ3 j with h | h
    · left
      constructor <;> omega
    · right
      constructor <;> omega
  -- every coordinate has another one
  have hne : ∀ i : Fin d, ∃ j : Fin d, j ≠ i := fun i => by
    by_cases hi : i.val = 0
    · exact ⟨⟨1, by omega⟩, fun h => by
        have := congrArg Fin.val h
        simp only at this
        omega⟩
    · exact ⟨⟨0, by omega⟩, fun h => hi (by rw [← h])⟩
  -- (B) any two hubs are joined in `M`
  have hB : ∀ j j', ReflTransGen (StepIn M LAdj) (Function.update c j (τ j))
      (Function.update c j' (τ j')) := by
    intro j j'
    by_cases hjj : j' = j
    · subst hjj
      exact ReflTransGen.refl
    have hp := update_mem_latBox_withinInf (hq j).1 (hq j).2 j' (hτ1 j') (hτ2 j') (hτc j')
    have e1 : Function.update (Function.update c j (τ j)) j' (τ j') j = τ j := by
      rw [Function.update_of_ne (Ne.symm hjj), Function.update_self]
    have e2 : Function.update (Function.update c j (τ j)) j' (τ j') j' = τ j' :=
      Function.update_self _ _ _
    refine (reflTransGen_shell_of_slab (hq j).1 (hq j).2 hp.1 hp.2
      ⟨j, hτside j _ _ (Function.update_self _ _ _) e1⟩).trans ?_
    exact reflTransGen_shell_of_slab hp.1 hp.2 (hq j').1 (hq j').2
      ⟨j', hτside j' _ _ e2 (Function.update_self _ _ _)⟩
  -- (A) every site of `M` is joined in `M` to some hub
  have hA : ∀ x ∈ M, ∃ j, ReflTransGen (StepIn M LAdj) x (Function.update c j (τ j)) := by
    rintro x ⟨hxΛ, ⟨i, hi⟩, hxc⟩
    obtain ⟨j, hji⟩ := hne i
    obtain ⟨α, hα⟩ : ∃ α, (c i + ρ₂ ≤ x i ∧ α = c i + ρ₂) ∨ (x i + ρ₂ ≤ c i ∧ α = c i - ρ₂) := by
      rw [le_abs] at hi
      rcases hi with h | h
      · exact ⟨c i + ρ₂, Or.inl ⟨by omega, rfl⟩⟩
      · exact ⟨c i - ρ₂, Or.inr ⟨by omega, rfl⟩⟩
    have hxi := hxΛ i
    have hci := hc i
    have hp := update_mem_latBox_withinInf (hq j).1 (hq j).2 i (v := α)
      (by rcases hα with h | h <;> omega) (by rcases hα with h | h <;> omega) (by
        rw [abs_le]
        rcases hα with h | h <;> constructor <;> omega)
    have e1 : Function.update (Function.update c j (τ j)) i α i = α := Function.update_self _ _ _
    have e2 : Function.update (Function.update c j (τ j)) i α j = τ j := by
      rw [Function.update_of_ne hji, Function.update_self]
    refine ⟨j, (reflTransGen_shell_of_slab hxΛ hxc hp.1 hp.2 ⟨i, ?_⟩).trans ?_⟩
    · rw [e1]
      rcases hα with h | h
      · left
        constructor <;> omega
      · right
        constructor <;> omega
    · exact reflTransGen_shell_of_slab hp.1 hp.2 (hq j).1 (hq j).2
        ⟨j, hτside j _ _ e2 (Function.update_self _ _ _)⟩
  intro x hx y hy
  obtain ⟨j, hj⟩ := hA x hx
  obtain ⟨j', hj'⟩ := hA y hy
  exact hj.trans ((hB j j').trans (reflTransGen_lAdj_symm hj'))

/-- **MA7 D-SHELL, chain form** (as consumed by `BoxSurgery` in MA7 D-4.9 (4)–(5)): two sites of
the shell `M = {x ∈ Λ : ρ₂ ≤ |x - c|_∞ ≤ ρ₁}` are the endpoints of an L-chain of sites of `M`. -/
theorem exists_shell_chain (hd : 2 ≤ d) (hρ₂ : 1 ≤ ρ₂) (hρ : ρ₂ < ρ₁) (hc : c ∈ latBox a b)
    (hside : ∀ i, c i + ρ₁ ≤ b i ∨ a i ≤ c i - ρ₁) {u v : Zd d}
    (hu : u ∈ {x | x ∈ latBox a b ∧ (∃ i, ρ₂ ≤ |x i - c i|) ∧ WithinInf ρ₁ x c})
    (hv : v ∈ {x | x ∈ latBox a b ∧ (∃ i, ρ₂ ≤ |x i - c i|) ∧ WithinInf ρ₁ x c}) :
    ∃ γ : List (Zd d), γ.IsChain LAdj ∧ γ.head? = some u ∧ γ.getLast? = some v ∧
      ∀ x ∈ γ, x ∈ latBox a b ∧ (∃ i, ρ₂ ≤ |x i - c i|) ∧ WithinInf ρ₁ x c :=
  exists_lAdj_chain_of_reflTransGen hu (shellLatticeConn hd hρ₂ hρ hc hside u hu v hv)

end Shell

end DGZ

end HigherDimLQGMetric
