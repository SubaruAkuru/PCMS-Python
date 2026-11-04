/-
# 标准模型（ℤ 版）：`ElderAbove` 与 `ElderBelow` 的相容性

`Model.lean` 用 `Nat × Nat` 构造的模型满足原文全部公理，但**不满足** `ElderAbove`
（第 `0` 号是最年长的，没有兄姐），故它恰好是"`EY ≠ S + I`"的反例。

本文件把索引从 `Nat` 换成 `ℤ`（**双向无限**），其余不变。于是每个兄弟类
都序同构于 `(ℤ, <)`，没有最大元也没有最小元，从而

* `ElderAbove` 与 `ElderBelow` **同时成立**；
* 由 `Unbounded.EY_eq`、`Unbounded.YE_eq` 立即得到
  `EY = S + I` 与 `YE = S + I`。

**结论**：补充公理 (A3a)、(A3a′) 与原公理 (A1)–(A7)+(B1)–(B4) 是**相容**的。
-/

import Unbounded
import Model

namespace PCMS

/-- ℤ 版模型的人：`(代, 编号)`，两坐标都取 `ℤ`。 -/
abbrev MZ : Type := Int × Int

namespace ModelZ

/-- 父母关系：第 `n` 代的人的父母是第 `n+1` 代的第 0、1 号。 -/
def par : Rel MZ := fun x y => y = (x.1 + 1, (0 : Int)) ∨ y = (x.1 + 1, (1 : Int))

/-- 配偶关系：同代第 0、1 号配成一对。 -/
def mate : Rel MZ := fun x y =>
  (x.2 = (0 : Int) ∧ y = (x.1, (1 : Int))) ∨
  (x.2 = (1 : Int) ∧ y = (x.1, (0 : Int)))

/-- 兄姐关系：同代内编号小者为长。 -/
def elder : Rel MZ := fun x y => x.1 = y.1 ∧ y.2 < x.2

theorem par_fst {x y : MZ} (h : par x y) : y.1 = x.1 + 1 := by
  rcases h with h | h <;> rw [h]

theorem par_snd {x y : MZ} (h : par x y) : y.2 = 0 ∨ y.2 = 1 := by
  rcases h with h | h
  · exact Or.inl (by rw [h])
  · exact Or.inr (by rw [h])

theorem par_two (p : MZ) : ∃ a b, a ≠ b ∧ par p a ∧ par p b :=
  ⟨(p.1 + 1, 0), (p.1 + 1, 1), by simp [Prod.ext_iff], Or.inl rfl, Or.inr rfl⟩

theorem mate_of_common_child {p q r : MZ} (hpq : p ≠ q)
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

theorem mate_unique {p q r : MZ} (hq : mate p q) (hr : mate p r) : q = r := by
  simp only [mate] at hq hr
  rcases hq with ⟨h0, hq⟩ | ⟨h1, hq⟩
  · rcases hr with ⟨-, hr⟩ | ⟨h1', -⟩
    · rw [hq, hr]
    · omega
  · rcases hr with ⟨h0', -⟩ | ⟨-, hr⟩
    · omega
    · rw [hq, hr]

theorem elder_trans {p q r : MZ} (hpq : elder p q) (hqr : elder q r) : elder p r := by
  obtain ⟨h1, h2⟩ := hpq
  obtain ⟨h3, h4⟩ := hqr
  exact ⟨h1.trans h3, by omega⟩

theorem elder_xor {p q : MZ} (hpq : elder p q) : ¬ elder q p := by
  obtain ⟨-, h⟩ := hpq
  intro h'
  obtain ⟨-, h''⟩ := h'
  omega

theorem elder_sib {p q : MZ} (h : elder p q ∨ elder q p) :
    ∃ r, par p r ∧ par q r ∧ p ≠ q := by
  have hne : p ≠ q := by
    intro he
    rcases h with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [he] at h2 <;> exact Int.lt_irrefl _ h2
  rcases h with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact ⟨(p.1 + 1, 0), Or.inl rfl, by rw [h1]; exact Or.inl rfl, hne⟩
  · exact ⟨(p.1 + 1, 0), Or.inl rfl, by rw [← h1]; exact Or.inl rfl, hne⟩

theorem sib_common_parent {p q : MZ} (hpq : p ≠ q)
    (h : ∃ r, par p r ∧ par q r) : elder p q ∨ elder q p := by
  obtain ⟨r, hp, hq⟩ := h
  have hp1 := par_fst hp
  have hq1 := par_fst hq
  have hlevel : p.1 = q.1 := by omega
  have hidx : p.2 ≠ q.2 := by
    intro he; exact hpq (Prod.ext hlevel he)
  rcases Int.lt_or_gt_of_ne hidx with h' | h'
  · exact Or.inr ⟨hlevel.symm, h'⟩
  · exact Or.inl ⟨hlevel, h'⟩

theorem sib_two (p : MZ) :
    ∃ a b, a ≠ b ∧ (elder p a ∨ elder a p) ∧ (elder p b ∨ elder b p) :=
  ⟨(p.1, p.2 + 1), (p.1, p.2 + 2), by simp [Prod.ext_iff],
    Or.inr ⟨rfl, by omega⟩, Or.inr ⟨rfl, by omega⟩⟩

/-- **人人有兄姐**（ℤ 无下界，故 `p.2 - 1` 总存在）。 -/
theorem elder_above (p : MZ) : ∃ q, elder p q :=
  ⟨(p.1, p.2 - 1), ⟨rfl, by omega⟩⟩

/-- **人人有弟妹**（ℤ 无上界）。 -/
theorem elder_below (p : MZ) : ∃ q, elder q p :=
  ⟨(p.1, p.2 + 1), ⟨rfl, by omega⟩⟩

/-- **相容性**：该结构满足原文全部公理。 -/
def kin : Kin MZ where
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

/-- 该模型满足 `ElderAbove`。 -/
theorem elderAbove : ElderAbove kin := elder_above

/-- 该模型满足 `ElderBelow`。 -/
theorem elderBelow : ElderBelow kin := elder_below

/-- **在该模型中 `EY = S + I` 成立**。 -/
theorem EY_holds (p r : MZ) : (kin.E * kin.Y) p r ↔ (kin.S + 1) p r :=
  kin.EY_eq elderAbove p r

/-- **在该模型中 `YE = S + I` 成立**。 -/
theorem YE_holds (p r : MZ) : (kin.Y * kin.E) p r ↔ (kin.S + 1) p r :=
  kin.YE_eq elderBelow p r

end ModelZ

end PCMS
