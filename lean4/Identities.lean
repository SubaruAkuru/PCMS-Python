/-
# §1.3 复合亲属关系式的简化等式

原文列出五条等式并声明"证明过程均略去"。本文件给出全部证明。

核心工具是
* `Kin.par_cases` —— 每人**恰有**两个父母（由 (A3)P + (A5) + (A6)）；
* `Kin.par_eq_of_sib'` —— 兄弟姐妹必为**全同胞**（父母相同）。

在原文 (A1)–(A7) 之下的结论：
* `PC = S + I` ✓
* `SS = S + I` ✓
* `PM = P` ✓
* `SP = P` ✓
* `CP ⊆ M + I` ✓（等号需 `MateCommonChild`，见 `Coupled.lean`）
-/

import Kin

namespace PCMS

universe u

namespace Kin

variable {P : Type u} (K : Kin P)

/-- 每人**恰有**两个父母：给定两个不同的父母，任何父母都必是这两者之一。 -/
theorem par_cases {x a b y : P} (hab : a ≠ b)
    (ha : K.par x a) (hb : K.par x b) (hy : K.par x y) : y = a ∨ y = b := by
  by_cases hya : y = a
  · exact Or.inl hya
  · by_cases hyb : y = b
    · exact Or.inr hyb
    · exact absurd (K.par_unique hab (fun h => hya h.symm) (fun h => hyb h.symm) ha hb hy)
        (by simp)

/-- 兄弟姐妹的父母集合相同（**全同胞定理**）。

证明：设 `p ≠ q` 有共同父母 `a`。取 `p` 的另一个父母 `r`（`r ≠ a`）与 `q` 的
另一个父母 `s`（`s ≠ a`）。由 (A5)，`a` 与 `r` 共有子女 `p` 故互为配偶，
`a` 与 `s` 共有子女 `q` 故互为配偶；由 (A6) 得 `r = s`。
再由 `par_cases`，`p` 的每个父母都只能是 `a` 或 `r`，而 `q` 的父母正是 `a`、`r`。 -/
theorem par_eq_of_sib' {p q a : P} (_hpq : p ≠ q)
    (hp : K.par p a) (hq : K.par q a) : ∀ r, K.par p r ↔ K.par q r := by
  obtain ⟨r, har, hpr⟩ := K.par_exists_second hp
  obtain ⟨s, has, hqs⟩ := K.par_exists_second hq
  have mar : K.mate a r := K.parents_mate har hp hpr
  have mas : K.mate a s := K.parents_mate has hq hqs
  have hrs : r = s := K.mate_unique mar mas
  subst hrs
  intro y
  constructor
  · intro hy
    rcases K.par_cases har hp hpr hy with h | h
    · subst h; exact hq
    · subst h; exact hqs
  · intro hy
    rcases K.par_cases har hq hqs hy with h | h
    · subst h; exact hp
    · subst h; exact hpr

/-- 兄弟姐妹的父母集合相同（`S` 版本）。 -/
theorem par_eq_of_S {p q : P} (h : K.S p q) : ∀ r, K.par p r ↔ K.par q r := by
  obtain ⟨⟨a, hp, hq⟩, hpq⟩ := (K.S_iff_common p q).1 h
  exact K.par_eq_of_sib' hpq hp hq

/-- 由 (A3)S 取到一个与 `r` 不同的兄弟。 -/
theorem exists_sib_ne (p r : P) : ∃ q, K.S p q ∧ q ≠ r := by
  obtain ⟨a, b, hab, ha, hb⟩ := K.sib_two p
  by_cases har : a = r
  · exact ⟨b, hb, fun hbr => hab (har.trans hbr.symm)⟩
  · exact ⟨a, ha, har⟩

/-! ## ① `PC = S + I` -/

/-- `PC ⊆ S + I`：`p` 的父母的子女或是 `p` 本人，或是 `p` 的兄弟姐妹。 -/
theorem PC_subset (p r : P) (h : (K.par * K.C) p r) : K.S p r ∨ r = p := by
  obtain ⟨q, hpq, hrq⟩ := h
  by_cases hrp : r = p
  · exact Or.inr hrp
  · exact Or.inl (K.sib_common_parent (fun h' => hrp h'.symm) ⟨q, hpq, hrq⟩)

/-- `S + I ⊆ PC`。 -/
theorem S_I_subset (p r : P) (h : K.S p r ∨ r = p) : (K.par * K.C) p r := by
  rcases h with hs | hrp
  · obtain ⟨⟨q, hpq, hrq⟩, _⟩ := (K.S_iff_common p r).1 hs
    exact ⟨q, hpq, hrq⟩
  · rw [hrp]
    obtain ⟨q, hpq⟩ := K.par_nonempty p
    exact ⟨q, hpq, hpq⟩

/-- **① 的第一式**：`PC = S + I`。 -/
theorem PC_eq (p r : P) : (K.par * K.C) p r ↔ (K.S + 1) p r := by
  constructor
  · intro h
    rcases K.PC_subset p r h with h' | h'
    · exact Or.inl h'
    · exact Or.inr h'
  · intro h
    rcases h with h' | h'
    · exact K.S_I_subset p r (Or.inl h')
    · exact K.S_I_subset p r (Or.inr h')

/-! ## ① 的第二式 `SS = S + I` -/

/-- `SS ⊆ S + I`：两个兄弟关系的复合仍是兄弟或自身。 -/
theorem SS_subset (p r : P) (h : (K.S * K.S) p r) : K.S p r ∨ r = p := by
  obtain ⟨q, hpq, hqr⟩ := h
  by_cases hrp : r = p
  · exact Or.inr hrp
  · refine Or.inl (K.sib_common_parent (fun h' => hrp h'.symm) ?_)
    obtain ⟨a, hpa⟩ := K.par_nonempty p
    exact ⟨a, hpa, (K.par_eq_of_S hqr a).1 ((K.par_eq_of_S hpq a).1 hpa)⟩

/-- `S + I ⊆ SS`。 -/
theorem S_I_subset_SS (p r : P) (h : K.S p r ∨ r = p) : (K.S * K.S) p r := by
  rcases h with hs | hrp
  · obtain ⟨q, hpq, hqr⟩ := K.exists_sib_ne p r
    refine ⟨q, hpq, K.sib_common_parent hqr ?_⟩
    obtain ⟨a, hpa⟩ := K.par_nonempty p
    exact ⟨a, (K.par_eq_of_S hpq a).1 hpa, (K.par_eq_of_S hs a).1 hpa⟩
  · rw [hrp]
    obtain ⟨q, hpq, _⟩ := K.exists_sib_ne p p
    exact ⟨q, hpq, (K.S_symm p q).1 hpq⟩

/-- **① 的第二式**：`SS = S + I`。 -/
theorem SS_eq (p r : P) : (K.S * K.S) p r ↔ (K.S + 1) p r := by
  constructor
  · intro h
    rcases K.SS_subset p r h with h' | h'
    · exact Or.inl h'
    · exact Or.inr h'
  · intro h
    rcases h with h' | h'
    · exact K.S_I_subset_SS p r (Or.inl h')
    · exact K.S_I_subset_SS p r (Or.inr h')

/-! ## ② `PM = P` 与 `SP = P` -/

/-- `PM ⊆ P`：`p` 的父母的配偶仍是 `p` 的父母。 -/
theorem PM_subset (p r : P) (h : (K.par * K.M) p r) : K.par p r := by
  obtain ⟨q, hpq, hqr⟩ := h
  obtain ⟨q', hqq', hpq'⟩ := K.par_exists_second hpq
  have m1 : K.mate q q' := K.parents_mate hqq' hpq hpq'
  have m2 : K.mate q r := hqr
  have hq'r : q' = r := K.mate_unique m1 m2
  exact hq'r ▸ hpq'

/-- `P ⊆ PM`。 -/
theorem P_subset_PM (p r : P) (h : K.par p r) : (K.par * K.M) p r := by
  obtain ⟨q, hrq, hpq⟩ := K.par_exists_second h
  exact ⟨q, hpq, K.parents_mate (fun h' => hrq h'.symm) hpq h⟩

/-- **② 的第一式**：`PM = P`。 -/
theorem PM_eq (p r : P) : (K.par * K.M) p r ↔ K.par p r :=
  ⟨K.PM_subset p r, K.P_subset_PM p r⟩

/-- `SP ⊆ P`：兄弟的父母就是自己的父母。 -/
theorem SP_subset (p r : P) (h : (K.S * K.par) p r) : K.par p r := by
  obtain ⟨q, hpq, hqr⟩ := h
  exact (K.par_eq_of_S hpq r).2 hqr

/-- `P ⊆ SP`。 -/
theorem P_subset_SP (p r : P) (h : K.par p r) : (K.S * K.par) p r := by
  obtain ⟨q, hpq, _⟩ := K.exists_sib_ne p p
  exact ⟨q, hpq, (K.par_eq_of_S hpq r).1 h⟩

/-- **② 的第二式**：`SP = P`。 -/
theorem SP_eq (p r : P) : (K.S * K.par) p r ↔ K.par p r :=
  ⟨K.SP_subset p r, K.P_subset_SP p r⟩

/-! ## ③ `CP ⊆ M + I` -/

/-- `C·P` 恰好是「有共同子女」的关系。 -/
theorem CP_iff (p q : P) :
    (K.C * K.par) p q ↔ ∃ r, K.par r p ∧ K.par r q := Iff.rfl

/-- `CP ⊆ M + I`：有共同子女的两人是配偶（或同一人）。 -/
theorem CP_subset (p q : P) (h : (K.C * K.par) p q) : K.M p q ∨ q = p := by
  obtain ⟨r, hrp, hrq⟩ := h
  by_cases hqp : q = p
  · exact Or.inr hqp
  · exact Or.inl (K.parents_mate (fun h' => hqp h'.symm) hrp hrq)

/-! ## ④ CS = C（在原文公理下即可证明） -/

/-- CS ⊆ C：p 的子女 q 的兄弟  仍是 p 的子女。

关键：由**全同胞定理**，q 与  的父母完全相同，故 p 也是  的父母。 -/
theorem CS_subset (p r : P) (h : (K.C * K.S) p r) : K.C p r := by
  obtain ⟨q, hpq, hqr⟩ := h
  exact (K.par_eq_of_S hqr p).1 hpq

/-- C ⊆ CS。 -/
theorem C_subset_CS (p r : P) (h : K.C p r) : (K.C * K.S) p r := by
  obtain ⟨q, hrq, _⟩ := K.exists_sib_ne r r
  exact ⟨q, (K.par_eq_of_S hrq p).1 h, (K.S_symm q r).2 hrq⟩

/-- **④ 的第二式**：CS = C。原文这一条是**正确**的。 -/
theorem CS_eq (p r : P) : (K.C * K.S) p r ↔ K.C p r :=
  ⟨K.CS_subset p r, K.C_subset_CS p r⟩

end Kin

end PCMS
