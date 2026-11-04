/-
# 使 `EY = YE = S + I` 成立的精确条件

原文（2026 更新）称 `EY = YE = E + I + Y`。本文已证该等式恒假
（`Model.EY_ne_S_add_I`），正确的目标应是 `EY = YE = S + I`（因 `E+Y=S` 是定义）。

本文件证明：

* `EY = S + I` **当且仅当** "人人都有兄姐"（`ElderAbove`）；
* `YE = S + I` **当且仅当** "人人都有弟妹"（`ElderBelow`）。

即：这两个等式**互相独立**，且各自**只差一条存在性公理**。

## 为什么是"人人有兄姐"？

在兄弟类上，`E` 是一个**严格全序**（`E p q` 读作"`q` 比 `p` 年长"）：
(B2) 传递、(B3) 三歧、(定理 3.6) 无自反。

于是
* `EY p r ⟺ ∃q, q 比 p 年长 ∧ q 比 r 年长` —— "`p` 与 `r` 有共同的长辈"；
* `S p r ⟺ p、r 是兄弟`。

在一个线性序中"任两人有共同上界" ⟺ "该序无最大元" ⟺ "每人都不是最年长的"
⟺ `ElderAbove`。顺便，`I p p` 要求 `EY p p`，即 `p` 有兄姐，也正是 `ElderAbove`。

**重要推论**：线性序若有限必有最大元，故 `EY = S + I` 迫使**每个兄弟类无限**。
换言之，任何有限模型都不可能满足它 —— 这是原文把它当作"可证等式"所掩盖的真代价。
-/

import Identities
import Order

namespace PCMS

universe u

/-- **补充公理 (A3a)**：人人都有兄姐。-/
def ElderAbove {P : Type u} (K : Kin P) : Prop := ∀ p : P, ∃ q : P, K.elder p q

/-- **补充公理 (A3a′)**：人人都有弟妹。-/
def ElderBelow {P : Type u} (K : Kin P) : Prop := ∀ p : P, ∃ q : P, K.elder q p

namespace Kin

variable {P : Type u} (K : Kin P)

/-! ### 辅助：`S p r` 时存在共同的长辈 / 晚辈 -/

/-- `S p r` 且人人有兄姐 ⟹ `p`、`r` 有共同的年长者。 -/
theorem common_elder_of_S (h : ElderAbove K) {p r : P} (hsr : K.S p r) :
    ∃ q, K.elder p q ∧ K.elder r q := by
  have hpr : p ≠ r := by
    intro he
    rw [he] at hsr
    rcases hsr with h' | h'
    · exact K.elder_xor h' h'
    · exact K.elder_xor h' h'
  obtain ⟨q0, hq0⟩ := h p
  have hS : K.S p q0 := Or.inl hq0
  have hpar : ∀ x, K.par q0 x ↔ K.par r x := by
    intro x
    exact ⟨fun hx => (K.par_eq_of_S hsr x).1 ((K.par_eq_of_S hS x).2 hx),
           fun hx => (K.par_eq_of_S hS x).1 ((K.par_eq_of_S hsr x).2 hx)⟩
  by_cases hqr : q0 = r
  · rw [hqr] at hq0
    obtain ⟨q1, hq1⟩ := h r
    exact ⟨q1, K.elder_trans hq0 hq1, hq1⟩
  · obtain ⟨a, ha⟩ := K.par_nonempty q0
    rcases K.sib_common_parent hqr ⟨a, ha, (hpar a).1 ha⟩ with h' | h'
    · -- `r` 比 `q0` 年长：再取一个比 `r` 年长的
      obtain ⟨q1, hq1⟩ := h r
      exact ⟨q1, K.elder_trans (K.elder_trans hq0 h') hq1, hq1⟩
    · -- `q0` 比 `r` 年长：`q0` 即为共同长辈
      exact ⟨q0, hq0, h'⟩

/-- `S p r` 且人人有弟妹 ⟹ `p`、`r` 有共同的年轻者。 -/
theorem common_younger_of_S (h : ElderBelow K) {p r : P} (hsr : K.S p r) :
    ∃ q, K.elder q p ∧ K.elder q r := by
  have hpr : p ≠ r := by
    intro he
    rw [he] at hsr
    rcases hsr with h' | h'
    · exact K.elder_xor h' h'
    · exact K.elder_xor h' h'
  obtain ⟨q0, hq0⟩ := h p
  have hS : K.S q0 p := Or.inl hq0
  have hpar : ∀ x, K.par q0 x ↔ K.par r x := by
    intro x
    exact ⟨fun hx => (K.par_eq_of_S hsr x).1 ((K.par_eq_of_S hS x).1 hx),
           fun hx => (K.par_eq_of_S hS x).2 ((K.par_eq_of_S hsr x).2 hx)⟩
  by_cases hqr : q0 = r
  · rw [hqr] at hq0
    obtain ⟨q1, hq1⟩ := h r
    exact ⟨q1, K.elder_trans hq1 hq0, hq1⟩
  · obtain ⟨a, ha⟩ := K.par_nonempty q0
    rcases K.sib_common_parent hqr ⟨a, ha, (hpar a).1 ha⟩ with h' | h'
    · -- `q0` 比 `r` 年轻：`q0` 即为共同晚辈
      exact ⟨q0, hq0, h'⟩
    · -- `r` 比 `q0` 年轻：再取一个比 `r` 年轻的
      obtain ⟨q1, hq1⟩ := h r
      exact ⟨q1, K.elder_trans (K.elder_trans hq1 h') hq0, hq1⟩

/-! ### 正向：公理 ⟹ 等式 -/

/-- **`ElderAbove` ⟹ `EY = S + I`**。 -/
theorem EY_eq (h : ElderAbove K) (p r : P) : (K.E * K.Y) p r ↔ (K.S + 1) p r := by
  constructor
  · intro hab
    rcases K.EY_subset p r hab with h' | h'
    · exact Or.inl h'
    · exact Or.inr h'
  · intro h'
    rcases h' with hsr | hrp
    · obtain ⟨q, h1, h2⟩ := K.common_elder_of_S h hsr
      exact ⟨q, h1, h2⟩
    · rw [hrp]
      obtain ⟨q, hq⟩ := h p
      exact ⟨q, hq, hq⟩

/-- **`ElderBelow` ⟹ `YE = S + I`**。 -/
theorem YE_eq (h : ElderBelow K) (p r : P) : (K.Y * K.E) p r ↔ (K.S + 1) p r := by
  constructor
  · intro hab
    rcases K.YE_subset p r hab with h' | h'
    · exact Or.inl h'
    · exact Or.inr h'
  · intro h'
    rcases h' with hsr | hrp
    · obtain ⟨q, h1, h2⟩ := K.common_younger_of_S h hsr
      exact ⟨q, h1, h2⟩
    · rw [hrp]
      obtain ⟨q, hq⟩ := h p
      exact ⟨q, hq, hq⟩

/-! ### 反向：等式 ⟹ 公理（故公理不可减弱） -/

/-- **`EY = S + I` ⟹ `ElderAbove`**。取 `p = r`：
`I p p` 成立，故 `EY p p` 成立，即 `∃q, E p q`。 -/
theorem elderAbove_of_EY (h : ∀ p r : P, (K.E * K.Y) p r ↔ (K.S + 1) p r) :
    ElderAbove K := by
  intro p
  have hpp : (K.S + 1) p p := Or.inr rfl
  obtain ⟨q, hq, -⟩ := (h p p).2 hpp
  exact ⟨q, hq⟩

/-- **`YE = S + I` ⟹ `ElderBelow`**。 -/
theorem elderBelow_of_YE (h : ∀ p r : P, (K.Y * K.E) p r ↔ (K.S + 1) p r) :
    ElderBelow K := by
  intro p
  have hpp : (K.S + 1) p p := Or.inr rfl
  obtain ⟨q, -, hq⟩ := (h p p).2 hpp
  exact ⟨q, hq⟩

end Kin

/-! ## 使 `CP = M + I` 成立的精确条件

需要**两条**，而且**不需要**"人人有配偶"：

* **(A9) 人人有子女** —— 用于 `I ⊆ CP`；
* **(A8) 配偶必有共同子女** —— 用于 `M ⊆ CP`。

（(A8) 与"配偶共同抚育" (A11) 在 (A3)P+(A5)+(A6) 之下互相等价：
两者都蕴含"一个人的所有子女的父母集合都等于他/她的配偶对"。）
-/

/-- **补充公理 (A8)**：配偶必有共同子女。-/
def MateCommonChild {P : Type u} (K : Kin P) : Prop :=
  ∀ {p q : P}, K.mate p q → ∃ r : P, K.par r p ∧ K.par r q

/-- **补充公理 (A9)**：人人有子女。-/
def ChildExists {P : Type u} (K : Kin P) : Prop := ∀ p : P, ∃ q : P, K.par q p

namespace Kin

variable {P : Type u} (K : Kin P)

/-- **`(A8)` + `(A9)` ⟹ `CP = M + I`**。 -/
theorem CP_eq (h9 : ChildExists K) (h8 : MateCommonChild K) (p q : P) :
    (K.C * K.par) p q ↔ (K.M + 1) p q := by
  constructor
  · exact K.CP_subset p q
  · rintro (hm | hqp)
    · obtain ⟨r, hrp, hrq⟩ := h8 hm
      exact ⟨r, hrp, hrq⟩
    · rw [hqp]
      obtain ⟨r, hr⟩ := h9 p
      exact ⟨r, hr, hr⟩

/-- **`CP = M + I` ⟹ `(A9)`**：取 `p = q`，`I p p` 成立故 `CP p p` 成立。 -/
theorem childExists_of_CP (h : ∀ p q : P, (K.C * K.par) p q ↔ (K.M + 1) p q) :
    ChildExists K := by
  intro p
  have hpp : (K.M + 1) p p := Or.inr rfl
  obtain ⟨r, -, hrp⟩ := (h p p).2 hpp
  exact ⟨r, hrp⟩

/-- **`CP = M + I` ⟹ `(A8)`**：`M p q` 给出 `CP p q`。 -/
theorem mateCommonChild_of_CP (h : ∀ p q : P, (K.C * K.par) p q ↔ (K.M + 1) p q) :
    MateCommonChild K := by
  intro p q hm
  obtain ⟨r, hrp, hrq⟩ := (h p q).2 (Or.inl hm)
  exact ⟨r, hrp, hrq⟩

end Kin

end PCMS
