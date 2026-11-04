/-
# A 组与 B 组能否同时成立？

本文件给出三条结构性结论，它们是回答该问题的关键。

1. `Complete.mate_exists_of_child_exists`：**(B2) 蕴含 (B3)**。
   "人人有子女"已经蕴含"人人有配偶"——子女的两个父母必互为配偶。
   故 B 组实际只有四条独立内容。

2. `KinCore.S_iff_par_eq`：**同胞类 = 父母集合相同的人**。
   整套结构可以完全用"父母对"描述。

3. `Complete.mate_par_iff`：**配偶在父母角色上可互换**。
   配合 1、2 得：每个同胞类恰是一个配偶对的子女全体，
   于是"同胞类 ↔ 配偶对"是双射。

结论（见 `COMBINED.md`）：**能同时成立，但只能在无限人口上成立。**
-/

import Core

namespace PCMS

universe u

namespace KinCore

variable {P : Type u} (K : KinCore P)

/-- **同胞类 = 父母集合相同的人**：`S p q` 当且仅当 `p ≠ q` 且二者父母完全相同。 -/
theorem S_iff_par_eq (p q : P) :
    K.S p q ↔ (p ≠ q ∧ ∀ r, K.par p r ↔ K.par q r) := by
  constructor
  · intro h
    obtain ⟨hne, a, ha, -⟩ := (K.S_iff p q).1 h
    exact ⟨hne, K.par_eq_of_S h⟩
  · rintro ⟨hne, hpar⟩
    obtain ⟨a, ha⟩ := K.par_nonempty p
    exact (K.S_iff p q).2 ⟨hne, ⟨a, ha, (hpar a).1 ha⟩⟩

end KinCore

namespace Complete

variable {P : Type u} {K : KinCore P}

/-- **(B2) 蕴含 (B3)**：人人有子女 ⟹ 人人有配偶。

证明：设 `r` 是 `p` 的子女。由定理 3.2，`r` 恰有两个父母，其一是 `p`，另一个记 `q ≠ p`；
由 (A5)，`p` 与 `q` 共有子女 `r`，故互为配偶。 -/
theorem mate_exists_of_child_exists (h : Complete K) (p : P) :
    ∃ q, K.mate p q := by
  obtain ⟨r, hr⟩ := h.child_exists p
  obtain ⟨q, hpq, hrq⟩ := K.par_exists_second hr
  exact ⟨q, K.parents_mate hpq hr hrq⟩

/-- **配偶在父母角色上可互换**：若 `p`、`q` 为配偶，则任何人是 `p` 的子女当且仅当是 `q` 的子女。 -/
theorem mate_par_iff (h : Complete K) {p q : P} (hm : K.mate p q) :
    ∀ r, K.par r p ↔ K.par r q := by
  intro r
  exact ⟨fun hr => h.mate_coparent hm hr,
         fun hr => h.mate_coparent (K.mate_symm hm) hr⟩

/-- **(A5) 与 (B1) 合起来：配偶 ⇔ 有共同子女**（p ≠ q 时）。
这正是"配偶对 = 父母对"的精确表述。 -/
theorem mate_iff_common_child (h : Complete K) {p q : P} (hpq : p ≠ q) :
    K.mate p q ↔ ∃ r, K.par r p ∧ K.par r q :=
  ⟨h.mate_common, fun ⟨r, hrp, hrq⟩ => K.parents_mate hpq hrp hrq⟩

end Complete

end PCMS
