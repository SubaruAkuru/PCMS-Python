/-
# 亲属树公理体系

对应原文：
* cv44165695 §1.1 公理 (A1)–(A7)
* cv1266515684416815108 「公理体系的更新」(B1)–(B4)

`Kin` 结构只记录**真正施加约束**的字段。按原文的方式，`C := P⁻¹`（(A4)）、
`Y := E⁻¹`（(B1)）、`S := E + Y` 均为定义；(A1)(A2) 在关系语义下是重言式，
故不列为字段（详见文档 §3.2）。
-/

import Rel

namespace PCMS

universe u

/-- 亲属树。字段即原文公理中被"结构性施加"的部分。 -/
structure Kin (P : Type u) where
  /-- 父母关系 `{P}_p`。-/
  par : Rel P
  /-- 配偶关系 `{M}_p`。-/
  mate : Rel P
  /-- 兄姐关系 `{E}_p`。-/
  elder : Rel P
  /-- **(A3)P** 每人至少两个互不相同的父母。-/
  par_two : ∀ p : P, ∃ a b : P, a ≠ b ∧ par p a ∧ par p b
  /-- **(A5)** 有共同子女的两人是配偶。-/
  mate_of_common_child : ∀ {p q r : P}, p ≠ q → par r p → par r q → mate p q
  /-- **(A6)** 配偶至多一人。-/
  mate_unique : ∀ {p q r : P}, mate p q → mate p r → q = r
  /-- **(B2)** 兄姐关系传递。-/
  elder_trans : ∀ {p q r : P}, elder p q → elder q r → elder p r
  /-- **(B3)** 兄弟姐妹必分长幼（不能互相当对方的长辈）。-/
  elder_xor : ∀ {p q : P}, elder p q → ¬ elder q p
  /-- **(B4)** 有长幼关系者必然是兄弟姐妹。 -/
  elder_sib : ∀ {p q : P}, elder p q ∨ elder q p → ∃ r, par p r ∧ par q r ∧ p ≠ q
  /-- **(A7)** 兄弟姐妹恰为有共同父母者。 -/
  sib_common_parent : ∀ {p q : P}, p ≠ q → (∃ r, par p r ∧ par q r) →
    (elder p q ∨ elder q p)
  /-- **(A3)S** 每人至少两个兄弟姐妹。 -/
  sib_two : ∀ p : P, ∃ a b : P, a ≠ b ∧ (elder p a ∨ elder a p) ∧ (elder p b ∨ elder b p)

namespace Kin

variable {P : Type u} (K : Kin P)

/-- **(A4)** 子女关系 `C := P⁻¹`。-/
def C : Rel P := K.par⁻¹

/-- **(B1)** 弟妹关系 `Y := E⁻¹`。-/
def Y : Rel P := K.elder⁻¹

/-- 兄弟姐妹关系 `S := E + Y`。-/
def S : Rel P := K.elder + K.elder⁻¹

/-- 配偶关系。 -/
abbrev M : Rel P := K.mate

/-- 兄姐关系（别名）。 -/
abbrev E : Rel P := K.elder

/-- 父母关系（别名）。 -/
abbrev P' : Rel P := K.par

@[simp] theorem C_apply (p q : P) : K.C p q ↔ K.par q p := Iff.rfl
@[simp] theorem Y_apply (p q : P) : K.Y p q ↔ K.elder q p := Iff.rfl
@[simp] theorem S_apply (p q : P) : K.S p q ↔ K.elder p q ∨ K.elder q p := Iff.rfl
@[simp] theorem M_apply (p q : P) : K.M p q ↔ K.mate p q := Iff.rfl

/-- 兄弟姐妹关系是对称的（由定义）。 -/
theorem S_symm (p q : P) : K.S p q ↔ K.S q p := by
  simp only [S_apply]
  exact ⟨fun h => h.elim Or.inr Or.inl, fun h => h.elim Or.inr Or.inl⟩

/-- 兄弟关系不含自反（(B3) 的直接推论）。 -/
theorem not_elder_self (p : P) : ¬ K.elder p p :=
  fun h => K.elder_xor h h

/-- **(A7) 的两个方向**：`S` 就是「有共同父母且不同」的关系。 -/
theorem S_iff_common (p q : P) :
    K.S p q ↔ (∃ r, K.par p r ∧ K.par q r) ∧ p ≠ q := by
  constructor
  · intro h
    have hpq : p ≠ q := by
      intro hpq
      subst hpq
      exact K.elder_xor (h.elim id id) (h.elim id id)
    obtain ⟨r, hp, hq, _⟩ := K.elder_sib h
    exact ⟨⟨r, hp, hq⟩, hpq⟩
  · rintro ⟨⟨r, hp, hq⟩, hpq⟩
    exact K.sib_common_parent hpq ⟨r, hp, hq⟩

/-- 每人都有父母。 -/
theorem par_nonempty (p : P) : ∃ a, K.par p a := by
  obtain ⟨a, _, _, ha, _⟩ := K.par_two p
  exact ⟨a, ha⟩

/-! ### 定理 1：每人恰有两个父母 -/

/-- **每人至多两个父母.** 若 `a, b, c` 是 `x` 的三个**两两不同**的父母，
则由 (A5) 得 `a` 与 `b` 互为配偶、`a` 与 `c` 互为配偶，由 (A6) 得 `b = c`，
与 `b ≠ c` 矛盾。 -/
theorem par_unique {x a b c : P}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hpa : K.par x a) (hpb : K.par x b) (hpc : K.par x c) : False := by
  have m1 : K.mate a b := K.mate_of_common_child hab hpa hpb
  have m2 : K.mate a c := K.mate_of_common_child hac hpa hpc
  exact hbc (K.mate_unique m1 m2)

/-- 给定一个父母，必能取到另一个互不相同的父母。 -/
theorem par_exists_second {x : P} {a : P} (ha : K.par x a) :
    ∃ b, a ≠ b ∧ K.par x b := by
  obtain ⟨b, c, hbc, hb, hc⟩ := K.par_two x
  by_cases hba : b = a
  · refine ⟨c, ?_, hc⟩
    intro h
    exact hbc (h ▸ hba.symm ▸ rfl)
  · exact ⟨b, fun h => hba h.symm, hb⟩

/-- 一个孩子的两个不同父母互为配偶。 -/
theorem parents_mate {x a b : P} (hab : a ≠ b) (ha : K.par x a) (hb : K.par x b) :
    K.mate a b :=
  K.mate_of_common_child hab ha hb

end Kin

end PCMS
