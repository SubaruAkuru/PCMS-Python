/-
# 一致性模型：`KinCore` 的模型

对应 `AXIOMS.md` §8.1。用 `Nat × Nat` 构造，逐条验证 (A1)–(A9)。

该模型**不满足** (B2)、(B3)、(B4)（第 `0` 号无兄姐、`i ≥ 2` 者无子女），
这与 `ModelZ.lean` 中把 `Nat` 换成 `Int` 后 (B4)、(B5) 成立的观察一致。
-/

import Core
import Model

namespace PCMS

namespace Model

/-- `mate` 对称。 -/
theorem mate_symm' {p q : M3} (h : mate p q) : mate q p := by
  simp only [mate] at h ⊢
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h2] at *
    exact Or.inr ⟨rfl, Prod.ext rfl h1⟩
  · rw [h2] at *
    exact Or.inl ⟨rfl, Prod.ext rfl h1⟩

/-- `mate` 无自反。 -/
theorem mate_irrefl' (p : M3) : ¬ mate p p := by
  simp only [mate]
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · have h : p.2 = 1 := by rw [h2]
    omega
  · have h : p.2 = 0 := by rw [h2]
    omega

/-- **(A6)** 的双向形式。 -/
theorem sib_iff' {p q : M3} :
    (elder p q ∨ elder q p) ↔ p ≠ q ∧ ∃ r, par p r ∧ par q r := by
  constructor
  · intro h
    obtain ⟨r, h1, h2, h3⟩ := elder_sib h
    exact ⟨h3, ⟨r, h1, h2⟩⟩
  · rintro ⟨hne, ⟨r, h1, h2⟩⟩
    exact sib_common_parent hne ⟨r, h1, h2⟩

/-- **(A1)–(A9) 相容**：`Nat × Nat` 模型满足全部结构公理。 -/
def kinCore : KinCore M3 where
  par := par
  mate := mate
  elder := elder
  two_parents := par_two
  mate_symm := mate_symm'
  mate_unique := mate_unique
  mate_irrefl := mate_irrefl'
  mate_of_coparent := mate_of_common_child
  sib_iff := sib_iff'
  elder_trans := elder_trans
  sib_two := sib_two

/-- 该模型中 (B1) 成立（配偶共同抚育）。 -/
theorem mate_coparent_holds {p q r : M3} (hm : kinCore.mate p q)
    (hp : kinCore.par r p) : kinCore.par r q := by
  simp only [kinCore, mate] at hm
  simp only [kinCore, par] at hp ⊢
  rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h2]
    rcases hp with hp | hp
    · rw [hp]; right; rfl
    · rw [hp]; right; rfl
  · rw [h2]
    rcases hp with hp | hp
    · rw [hp]; left; rfl
    · rw [hp]; left; rfl

end Model

end PCMS
