/-
# §1.5 `EY` 的真实等式

原文（2026 更新）称：

> 我们可以证明 `EY = YE = E + I + Y`.

本文件证明：**该等式对任何非退化模型都不成立**。

* `E + Y = S` 是**定义**（`S := E + Y`），不是定理；
* 正确的关系是 `EY ⊆ S + I` 与 `YE ⊆ S + I`（本文件给出证明）；
* 反向的 `S ⊆ EY` 不成立：它要求任意两个兄弟有**共同**的兄姐/弟妹，
  即兄弟类至少 3 人且"两端点"也有共同的长辈。`Model.lean` 中的
  `EY_ne_S`、`EY_ne_S_add_I` 给出机器验证的反例。

## 证 `EY ⊆ S + I` 的思路

`EY p r ⟺ ∃q, E p q ∧ E r q`（`p`、`r` 有共同兄姐 `q`）。
由 (B4) 与全同胞定理，`E p q` 给出 `par p = par q`，`E r q` 给出 `par r = par q`，
故 `par p = par r`；若 `p ≠ r` 则由 (A7) 得 `S p r`，否则 `r = p`。
-/

import Identities

namespace PCMS

universe u

namespace Kin

variable {P : Type u} (K : Kin P)

/-- `E + Y = S` 是定义。 -/
theorem E_add_Y : K.E + K.Y = K.S := rfl

/-- **`EY ⊆ S + I`**。 -/
theorem EY_subset (p r : P) (h : (K.E * K.Y) p r) : K.S p r ∨ r = p := by
  have h' : ∃ q, K.elder p q ∧ K.elder r q := h
  obtain ⟨q, hpq, hrq⟩ := h'
  by_cases hrp : r = p
  · exact Or.inr hrp
  · refine Or.inl (K.sib_common_parent (fun h' => hrp h'.symm) ?_)
    -- `E p q → S p q` 与 `E r q → S r q`，故 `par p = par q = par r`
    have hspq : K.S p q := Or.inl hpq
    have hsrq : K.S r q := Or.inl hrq
    obtain ⟨a, hpa⟩ := K.par_nonempty p
    exact ⟨a, hpa, (K.par_eq_of_S hsrq a).2 ((K.par_eq_of_S hspq a).1 hpa)⟩

/-- **`YE ⊆ S + I`**。 -/
theorem YE_subset (p r : P) (h : (K.Y * K.E) p r) : K.S p r ∨ r = p := by
  have h' : ∃ q, K.elder q p ∧ K.elder q r := h
  obtain ⟨q, hqp, hqr⟩ := h'
  by_cases hrp : r = p
  · exact Or.inr hrp
  · refine Or.inl (K.sib_common_parent (fun h' => hrp h'.symm) ?_)
    have hsqp : K.S q p := Or.inl hqp
    have hsqr : K.S q r := Or.inl hqr
    obtain ⟨a, hqa⟩ := K.par_nonempty q
    exact ⟨a, (K.par_eq_of_S hsqp a).1 hqa, (K.par_eq_of_S hsqr a).1 hqa⟩

/-- `E` 与 `Y` 不相交（(B3) 的直接推论）。 -/
theorem elder_disjoint (p q : P) : ¬ (K.E p q ∧ K.Y p q) := by
  rintro ⟨h1, h2⟩
  exact K.elder_xor h1 h2

end Kin

end PCMS
