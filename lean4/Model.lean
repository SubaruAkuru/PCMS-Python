/-
# 标准模型：公理体系的相容性

原文称"可以通过构造符合全部公理的亲属树，来证明公理内部不存在矛盾"，并给出一个
实数集上的构造，但该构造只描述了 `C` 与 `M` 的取法，并未逐条验证 `E`、`Y`、`S`
的公理。本文件给出一个**完整且已在 Lean 中逐条验证**的模型。

## 构造

取 `P := Nat × Nat`，把 `(n, i)` 读作「第 `n` 代、第 `i` 个孩子」。

* **父母**：`par (n,i) = {(n+1, 0), (n+1, 1)}`；
* **配偶**：`mate` 只把 `(n,0)` 与 `(n,1)` 配成一对；
* **兄姐**：同一代内按编号排序，`elder (n,i) (m,j) ⟺ n = m ∧ j < i`。

于是
* 每人恰有 2 个父母（(A3)P、(A5)、(A6)）；
* 每代之内人人互为全同胞（(A7)、(A3)S）；
* 长幼是同一代上的严格全序（(B2)–(B4)）。

## 推论

在此模型中 `EY ≠ S + I`，从而**原文 §1.5 的 `EY = YE = E + I + Y` 不成立**。
-/

import Identities

namespace PCMS

/-- 模型的人：`(代, 编号)`。 -/
abbrev M3 : Type := Nat × Nat

namespace Model

/-- 父母关系。 -/
def par : Rel M3 := fun x y => y = (x.1 + 1, 0) ∨ y = (x.1 + 1, 1)

/-- 配偶关系：只把同代的第 0、1 号配成一对。 -/
def mate : Rel M3 := fun x y =>
  (x.2 = 0 ∧ y = (x.1, 1)) ∨ (x.2 = 1 ∧ y = (x.1, 0))

/-- 兄姐关系：同代内编号小者为长。 -/
def elder : Rel M3 := fun x y => x.1 = y.1 ∧ y.2 < x.2

/-! ### 关于 `par` 的两条基本事实 -/

theorem par_fst {x y : M3} (h : par x y) : y.1 = x.1 + 1 := by
  rcases h with h | h <;> rw [h]

theorem par_snd {x y : M3} (h : par x y) : y.2 = 0 ∨ y.2 = 1 := by
  rcases h with h | h
  · exact Or.inl (by rw [h])
  · exact Or.inr (by rw [h])

/-! ### 逐条验证公理 -/

theorem par_two (p : M3) : ∃ a b, a ≠ b ∧ par p a ∧ par p b :=
  ⟨(p.1 + 1, 0), (p.1 + 1, 1), by simp [Prod.ext_iff], Or.inl rfl, Or.inr rfl⟩

theorem mate_of_common_child {p q r : M3} (hpq : p ≠ q)
    (hp : par r p) (hq : par r q) : mate p q := by
  have hp1 := par_fst hp
  have hq1 := par_fst hq
  have hp2 := par_snd hp
  have hq2 := par_snd hq
  simp only [mate]
  rcases hp2 with hp2 | hp2 <;> rcases hq2 with hq2 | hq2
  · exact absurd (Prod.ext (by omega) (by omega)) hpq
  · exact Or.inl ⟨hp2, Prod.ext (by omega) hq2⟩
  · exact Or.inr ⟨hp2, Prod.ext (by omega) hq2⟩
  · exact absurd (Prod.ext (by omega) (by omega)) hpq

theorem mate_unique {p q r : M3} (hq : mate p q) (hr : mate p r) : q = r := by
  simp only [mate] at hq hr
  rcases hq with ⟨h0, hq⟩ | ⟨h1, hq⟩
  · rcases hr with ⟨-, hr⟩ | ⟨h1', -⟩
    · rw [hq, hr]
    · omega
  · rcases hr with ⟨h0', -⟩ | ⟨-, hr⟩
    · omega
    · rw [hq, hr]

theorem elder_trans {p q r : M3} (hpq : elder p q) (hqr : elder q r) : elder p r := by
  obtain ⟨h1, h2⟩ := hpq
  obtain ⟨h3, h4⟩ := hqr
  exact ⟨h1.trans h3, by omega⟩

theorem elder_xor {p q : M3} (hpq : elder p q) : ¬ elder q p := by
  obtain ⟨-, h⟩ := hpq
  intro h'
  obtain ⟨-, h''⟩ := h'
  omega

theorem elder_sib {p q : M3} (h : elder p q ∨ elder q p) :
    ∃ r, par p r ∧ par q r ∧ p ≠ q := by
  have hne : p ≠ q := by
    intro he
    rcases h with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [he] at h2 <;> exact Nat.lt_irrefl _ h2
  rcases h with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact ⟨(p.1 + 1, 0), Or.inl rfl, by rw [h1]; exact Or.inl rfl, hne⟩
  · exact ⟨(p.1 + 1, 0), Or.inl rfl, by rw [← h1]; exact Or.inl rfl, hne⟩

theorem sib_common_parent {p q : M3} (hpq : p ≠ q)
    (h : ∃ r, par p r ∧ par q r) : elder p q ∨ elder q p := by
  obtain ⟨r, hp, hq⟩ := h
  have hp1 := par_fst hp
  have hq1 := par_fst hq
  have hlevel : p.1 = q.1 := by omega
  have hidx : p.2 ≠ q.2 := by
    intro he; exact hpq (Prod.ext hlevel he)
  rcases Nat.lt_or_gt_of_ne hidx with h' | h'
  · exact Or.inr ⟨hlevel.symm, h'⟩
  · exact Or.inl ⟨hlevel, h'⟩

theorem sib_two (p : M3) :
    ∃ a b, a ≠ b ∧ (elder p a ∨ elder a p) ∧ (elder p b ∨ elder b p) :=
  ⟨(p.1, p.2 + 1), (p.1, p.2 + 2), by simp [Prod.ext_iff],
    Or.inr ⟨rfl, by omega⟩, Or.inr ⟨rfl, by omega⟩⟩

/-- **公理体系相容**：上述结构满足原文全部公理。 -/
def kin : Kin M3 where
  par := par
  mate := mate
  elder := elder
  par_two := par_two
  mate_of_common_child := mate_of_common_child
  mate_unique := mate_unique
  elder_trans := elder_trans
  elder_xor := elder_xor
  elder_sib := elder_sib
  sib_common_parent := sib_common_parent
  sib_two := sib_two

/-! ### 用模型反驳 `EY = E + I + Y` -/

/-- `EY (0,1) (0,0)` 不成立：`(0,0)` 没有兄姐，故不存在二者的共同兄姐。 -/
theorem EY_false_mem : ¬ (kin.E * kin.Y) (0, 1) (0, 0) := by
  rintro ⟨q, h1, h2⟩
  simp only [Kin.E, Kin.Y, kin, elder, Rel.inv_apply] at h1 h2
  obtain ⟨-, h2'⟩ := h1
  omega

/-- 但 `(0,1)` 与 `(0,0)` 确是兄弟。 -/
theorem S_true_mem : kin.S (0, 1) (0, 0) := by
  show elder (0, 1) (0, 0) ∨ elder (0, 0) (0, 1)
  exact Or.inl ⟨rfl, by omega⟩

/-- **`EY ≠ E + Y`**（从而原文的 `EY = E + I + Y` 不成立）。 -/
theorem EY_ne_S : kin.E * kin.Y ≠ kin.S := by
  intro h
  have hb : (kin.E * kin.Y) (0, 1) (0, 0) ↔ kin.S (0, 1) (0, 0) := by rw [h]
  exact EY_false_mem (hb.2 S_true_mem)

/-- 更强：`EY` 甚至不等于 `S + I`。 -/
theorem EY_ne_S_add_I : kin.E * kin.Y ≠ kin.S + 1 := by
  intro h
  have hb : (kin.E * kin.Y) (0, 1) (0, 0) ↔ (kin.S + 1) (0, 1) (0, 0) := by rw [h]
  exact EY_false_mem (hb.2 (Or.inl S_true_mem))

end Model

end PCMS
