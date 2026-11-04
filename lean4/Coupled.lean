/-
# 补全的公理体系（`Coupled`）

§1.3 中有三条等式在原文 (A1)–(A7) 之下**不可证**（`Identities.lean` 只证到
`CP ⊆ M + I`）。原因是原文公理只给出

  「有共同子女 ⟹ 是配偶」（(A5)）

这**一个方向**，而没有给出反方向，也没有讨论"配偶是否共同抚育子女"。

本文件补三条公理，凑齐 §1.3 的全部等式：

* **(A9) 人人有子女**：`∀ p, ∃ q, par q p` —— 用于 `I ⊆ CP`；
* **(A10) 人人有配偶**：`∀ p, ∃ q, mate p q` —— 用于 `I ⊆ MM`；
* **(A11) 配偶同为父母**：`mate p q → par r p → par r q`
  —— 即"配偶共同抚育"，用于 `M _ C ⊆ C` 与 `M ⊆ C·P`。

在这三条之下，`M` 自动对称，(A5) 的逆命题也成立，于是
`MM = I`、`MC = C`、`CP = M + I` 全部得证。

> **(A11) 是最关键的补充。** 原文 §1.3 ④ 的 `MC = C` 与 ③ 的 `CP ⊇ M`
> 都依赖它；缺了它，一对"无子女夫妻"或"继子女"即可推翻等式。
-/

import Order

namespace PCMS

universe u

/-- 补全公理：使 §1.3 的等式全部成立所需的三条额外条件。 -/
structure Coupled {P : Type u} (K : Kin P) : Prop where
  /-- **(A9)** 人人有子女。-/
  child_exists : ∀ p : P, ∃ q : P, K.par q p
  /-- **(A10)** 人人有配偶。-/
  mate_exists : ∀ p : P, ∃ q : P, K.mate p q
  /-- **(A11)** 配偶同为父母：配偶共同抚育子女。-/
  mate_coparent : ∀ {p q r : P}, K.mate p q → K.par r p → K.par r q

namespace Coupled

variable {P : Type u} {K : Kin P}

/-- **(A11) ⟹ 配偶关系对称。** -/
theorem mate_symm (h : Coupled K) {p q : P} (hpq : K.mate p q) : K.mate q p := by
  obtain ⟨r, hr⟩ := h.child_exists p
  have h1 : K.par r q := h.mate_coparent hpq hr
  by_cases hpq' : p = q
  · rw [hpq'] at hpq ⊢
    exact hpq
  · exact K.parents_mate (fun h' => hpq' h'.symm) h1 hr

/-- **(A5) 的逆命题**：配偶必有共同子女。 -/
theorem mate_common_child (h : Coupled K) {p q : P} (hpq : K.mate p q) :
    ∃ r, K.par r p ∧ K.par r q := by
  obtain ⟨r, hr⟩ := h.child_exists p
  exact ⟨r, hr, h.mate_coparent hpq hr⟩

/-! ## ⑤ `MM = I` -/

/-- **⑤ `MM = I`**。 -/
theorem MM_eq (h : Coupled K) (p q : P) : (K.M * K.M) p q ↔ q = p := by
  constructor
  · rintro ⟨s, hps, hsq⟩
    have hsp : K.mate s p := h.mate_symm hps
    exact K.mate_unique hsq hsp
  · rintro rfl
    obtain ⟨s, hs⟩ := h.mate_exists q
    exact ⟨s, hs, h.mate_symm hs⟩

/-! ## ④ `MC = C` -/

/-- **④ 的第一式 `MC = C`**：配偶的子女就是自己的子女。 -/
theorem MC_eq (h : Coupled K) (p r : P) : (K.M * K.C) p r ↔ K.C p r := by
  constructor
  · rintro ⟨q, hpq, hqr⟩
    -- `hqr : K.C q r` 即 `K.par r q`
    exact h.mate_coparent (h.mate_symm hpq) hqr
  · intro hpr
    obtain ⟨q, hq⟩ := h.mate_exists p
    exact ⟨q, hq, h.mate_coparent hq hpr⟩

/-! ## ③ `CP = M + I` -/

/-- **③ `CP = M + I`**。 -/
theorem CP_eq (h : Coupled K) (p q : P) : (K.C * K.par) p q ↔ (K.M + 1) p q := by
  constructor
  · rintro ⟨r, hrp, hrq⟩
    by_cases hqp : q = p
    · exact Or.inr hqp
    · exact Or.inl (K.parents_mate (fun h' => hqp h'.symm) hrp hrq)
  · rintro (hm | hqp)
    · obtain ⟨r, hrp, hrq⟩ := h.mate_common_child hm
      exact ⟨r, hrp, hrq⟩
    · rw [hqp]
      obtain ⟨r, hr⟩ := h.child_exists p
      exact ⟨r, hr, hr⟩


/-! ## M³ = M -/

/-- 原文 §1.5 用到 M³ = M。它由 MM = I 立即推出。 -/
theorem M_cube_eq (h : Coupled K) : K.M * K.M * K.M = K.M := by
  have hmm : K.M * K.M = 1 := Rel.ext (fun p q => MM_eq h p q)
  rw [hmm, Rel.one_mul]

end Coupled

end PCMS
