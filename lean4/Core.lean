/-
# 亲属关系代数：公理体系（Lean 形式化）

与 `AXIOMS.md` 逐条对应。生成元 `P, C, M, E, Y, I, 0`，其中
`C := P⁻¹`、`Y := E⁻¹`、`S := E + Y` 均为**定义**（不占公理名额）。

## A 组：结构公理（8 条）

| 编号 | 内容 | 字段 |
|---|---|---|
| (A1) | 每人至少两个父母 | `two_parents` |
| (A2) | 配偶对称 | `mate_symm` |
| (A3) | 配偶唯一 | `mate_unique` |
| (A4) | 无自婚 | `mate_irrefl` |
| (A5) | 共子即配 | `mate_of_coparent` |
| (A6) | 同胞即共父母 | `sib_iff` |
| (A7) | 长幼传递 | `elder_trans` |
| (A8) | 同胞足数 | `sib_two` |

## B 组：完备化公理（5 条，可选）

| 编号 | 内容 | 字段 |
|---|---|---|
| (B1) | 配偶共育 | `mate_coparent` |
| (B2) | 人人有子女 | `child_exists` |
| (B3) | 人人有配偶 | `mate_exists` |
| (B4) | 人人有兄姐 | `elder_above` |
| (B5) | 人人有弟妹 | `elder_below` |

**注.** §2.4 中讨论过的"长幼限于同胞"（$E\subseteq S$）在 $S:=E+Y$ 之下是重言式，
故不列为公理；它有实质内容的部分已由 (A6) 承担。
-/

import Rel

namespace PCMS

universe u

/-- 亲属树的结构公理（A 组）。 -/
structure KinCore (P : Type u) where
  /-- 父母关系 `{P}_p`。 -/
  par : Rel P
  /-- 配偶关系 `{M}_p`。 -/
  mate : Rel P
  /-- 兄姐关系 `{E}_p`。 -/
  elder : Rel P
  /-- **(A1) 双亲性**：每人至少两个互不相同的父母。 -/
  two_parents : ∀ p : P, ∃ a b : P, a ≠ b ∧ par p a ∧ par p b
  /-- **(A2) 配偶对称**。 -/
  mate_symm : ∀ {p q : P}, mate p q → mate q p
  /-- **(A3) 配偶唯一**。 -/
  mate_unique : ∀ {p q r : P}, mate p q → mate p r → q = r
  /-- **(A4) 无自婚**。 -/
  mate_irrefl : ∀ p : P, ¬ mate p p
  /-- **(A5) 共子即配**。 -/
  mate_of_coparent : ∀ {p q r : P}, p ≠ q → par r p → par r q → mate p q
  /-- **(A6) 同胞即共父母**。 -/
  sib_iff : ∀ {p q : P}, (elder p q ∨ elder q p) ↔
    (p ≠ q ∧ ∃ r : P, par p r ∧ par q r)
  /-- **(A7) 长幼传递**。 -/
  elder_trans : ∀ {p q r : P}, elder p q → elder q r → elder p r
  /-- **(A8) 同胞足数**：每人至少两个同胞。 -/
  sib_two : ∀ p : P, ∃ a b : P, a ≠ b ∧ (elder p a ∨ elder a p) ∧
    (elder p b ∨ elder b p)

namespace KinCore

variable {P : Type u} (K : KinCore P)

/-! ## 派生记号 -/

/-- 子女 `C := P⁻¹`。 -/
def C : Rel P := K.par⁻¹

/-- 弟妹 `Y := E⁻¹`。 -/
def Y : Rel P := K.elder⁻¹

/-- 兄弟姐妹 `S := E + Y`。 -/
def S : Rel P := K.elder + K.elder⁻¹

@[simp] theorem C_apply (p q : P) : K.C p q ↔ K.par q p := Iff.rfl
@[simp] theorem Y_apply (p q : P) : K.Y p q ↔ K.elder q p := Iff.rfl
@[simp] theorem S_apply (p q : P) : K.S p q ↔ (K.elder p q ∨ K.elder q p) := Iff.rfl

/-- **(A6) 的等价形式**：`S` 恰是"有共同父母且不同"。 -/
theorem S_iff (p q : P) :
    K.S p q ↔ (p ≠ q ∧ ∃ r, K.par p r ∧ K.par q r) :=
  K.sib_iff

/-! ## §3.3 对称性与反自反 -/

/-- **定理 3.9（同胞对称）**。 -/
theorem S_symm (p q : P) : K.S p q ↔ K.S q p := by
  simp only [S_apply]
  exact ⟨fun h => h.elim Or.inr Or.inl, fun h => h.elim Or.inr Or.inl⟩

/-- **定理 3.7（长幼反自反）**。 -/
theorem not_elder_self (p : P) : ¬ K.elder p p := by
  intro h
  have h' : K.S p p := Or.inl h
  exact (K.S_iff p p).1 h' |>.1 rfl

/-- **定理 3.8（长幼反对称）**。 -/
theorem elder_asymm {p q : P} (h : K.elder p q) : ¬ K.elder q p := by
  intro h'
  exact K.not_elder_self p (K.elder_trans h h')

/-! ## §3.1 父母恰有两人 -/

/-- **定理 3.1（父母至多两人）**。 -/
theorem par_unique {x a b c : P} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hpa : K.par x a) (hpb : K.par x b) (hpc : K.par x c) : False := by
  have m1 : K.mate a b := K.mate_of_coparent hab hpa hpb
  have m2 : K.mate a c := K.mate_of_coparent hac hpa hpc
  exact hbc (K.mate_unique m1 m2)

/-- **定理 3.3（父母互为配偶）**。 -/
theorem parents_mate {x a b : P} (hab : a ≠ b) (ha : K.par x a) (hb : K.par x b) :
    K.mate a b :=
  K.mate_of_coparent hab ha hb

/-- **定理 3.4（第二个父母存在）**。 -/
theorem par_exists_second {x a : P} (ha : K.par x a) :
    ∃ b, a ≠ b ∧ K.par x b := by
  obtain ⟨b, c, hbc, hb, hc⟩ := K.two_parents x
  by_cases hba : b = a
  · refine ⟨c, ?_, hc⟩
    intro h
    exact hbc (hba.trans h)
  · exact ⟨b, fun h => hba h.symm, hb⟩

/-- 每人都有父母。 -/
theorem par_nonempty (p : P) : ∃ a, K.par p a := by
  obtain ⟨a, _, _, ha, _⟩ := K.two_parents p
  exact ⟨a, ha⟩

/-- **定理 3.5（父母的穷举）**。 -/
theorem par_cases {x a b y : P} (hab : a ≠ b)
    (ha : K.par x a) (hb : K.par x b) (hy : K.par x y) : y = a ∨ y = b := by
  by_cases hya : y = a
  · exact Or.inl hya
  · by_cases hyb : y = b
    · exact Or.inr hyb
    · exact absurd (K.par_unique hab (fun h => hya h.symm) (fun h => hyb h.symm)
        ha hb hy) (by simp)

/-! ## §3.2 全同胞定理 -/

/-- **定理 3.6（全同胞）**：同胞的父母完全相同。 -/
theorem par_eq_of_sib {p q a : P} (hp : K.par p a) (hq : K.par q a) :
    ∀ r, K.par p r ↔ K.par q r := by
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

/-- 同胞的父母集合相同（`S` 版）。 -/
theorem par_eq_of_S {p q : P} (h : K.S p q) : ∀ r, K.par p r ↔ K.par q r := by
  obtain ⟨_, ⟨a, hp, hq⟩⟩ := (K.S_iff p q).1 h
  exact K.par_eq_of_sib hp hq

/-! ## §3.4 长幼是严格全序 -/

/-- **定理 3.11（严格全序）**：在同胞类上，`E` 是反自反、传递、三歧的。 -/
theorem elder_strict_total {p q : P} (h : K.S p q) :
    (K.elder p q ∨ K.elder q p) ∧ ¬ (K.elder p q ∧ K.elder q p) := by
  refine ⟨(K.S_apply p q).1 h, ?_⟩
  rintro ⟨h2, h3⟩
  exact K.elder_asymm h2 h3

/-- 同胞存在一个与给定人不同的同胞（(A8) 的直接推论）。 -/
theorem exists_sib_ne (p r : P) : ∃ q, K.S p q ∧ q ≠ r := by
  obtain ⟨a, b, hab, ha, hb⟩ := K.sib_two p
  by_cases har : a = r
  · exact ⟨b, (K.S_apply p b).2 hb, fun hbr => hab (har.trans hbr.symm)⟩
  · exact ⟨a, (K.S_apply p a).2 ha, har⟩

end KinCore

/-! ## §4 复合关系式的简化等式 -/

namespace KinCore

variable {P : Type u} (K : KinCore P)

/-- **定理 4.1**：`PC = S + I`。 -/
theorem PC_eq (p r : P) : (K.par * K.C) p r ↔ (K.S + 1) p r := by
  constructor
  · intro h
    obtain ⟨q, hpq, hrq⟩ := h
    by_cases hrp : r = p
    · exact Or.inr hrp
    · exact Or.inl ((K.S_iff p r).2 ⟨fun h' => hrp h'.symm, ⟨q, hpq, hrq⟩⟩)
  · intro h
    rcases h with hs | hrp
    · obtain ⟨hn, ⟨q, hpq, hrq⟩⟩ := (K.S_iff p r).1 hs
      exact ⟨q, hpq, hrq⟩
    · rw [hrp]
      obtain ⟨q, hpq⟩ := K.par_nonempty p
      exact ⟨q, hpq, hpq⟩

/-- **定理 4.2**：`SS = S + I`。 -/
theorem SS_eq (p r : P) : (K.S * K.S) p r ↔ (K.S + 1) p r := by
  constructor
  · intro h
    obtain ⟨q, hpq, hqr⟩ := h
    by_cases hrp : r = p
    · exact Or.inr hrp
    · refine Or.inl ((K.S_iff p r).2 ⟨fun h' => hrp h'.symm, ?_⟩)
      obtain ⟨a, hpa⟩ := K.par_nonempty p
      exact ⟨a, hpa, (K.par_eq_of_S hqr a).1 ((K.par_eq_of_S hpq a).1 hpa)⟩
  · intro h
    rcases h with hs | hrp
    · obtain ⟨q, hpq, hqr⟩ := K.exists_sib_ne p r
      refine ⟨q, hpq, (K.S_iff q r).2 ⟨hqr, ?_⟩⟩
      obtain ⟨a, hpa⟩ := K.par_nonempty p
      exact ⟨a, (K.par_eq_of_S hpq a).1 hpa, (K.par_eq_of_S hs a).1 hpa⟩
    · rw [hrp]
      obtain ⟨q, hpq, _⟩ := K.exists_sib_ne p p
      exact ⟨q, hpq, (K.S_symm p q).1 hpq⟩

/-- **定理 4.3**：`PM = P`。 -/
theorem PM_eq (p r : P) : (K.par * K.mate) p r ↔ K.par p r := by
  constructor
  · intro h
    obtain ⟨q, hpq, hqr⟩ := h
    obtain ⟨q', hqq', hpq'⟩ := K.par_exists_second hpq
    have m1 : K.mate q q' := K.parents_mate hqq' hpq hpq'
    have hq'r : q' = r := K.mate_unique m1 hqr
    exact hq'r ▸ hpq'
  · intro h
    obtain ⟨q, hrq, hpq⟩ := K.par_exists_second h
    exact ⟨q, hpq, K.parents_mate (fun h' => hrq h'.symm) hpq h⟩

/-- **定理 4.4**：`SP = P`。 -/
theorem SP_eq (p r : P) : (K.S * K.par) p r ↔ K.par p r := by
  constructor
  · intro h
    obtain ⟨q, hpq, hqr⟩ := h
    exact (K.par_eq_of_S hpq r).2 hqr
  · intro h
    obtain ⟨q, hpq, _⟩ := K.exists_sib_ne p p
    exact ⟨q, hpq, (K.par_eq_of_S hpq r).1 h⟩

/-- **定理 4.5**：`CS = C`。 -/
theorem CS_eq (p r : P) : (K.C * K.S) p r ↔ K.C p r := by
  constructor
  · intro h
    obtain ⟨q, hpq, hqr⟩ := h
    exact (K.par_eq_of_S hqr p).1 hpq
  · intro h
    obtain ⟨q, hrq, _⟩ := K.exists_sib_ne r r
    exact ⟨q, (K.par_eq_of_S hrq p).1 h, (K.S_symm q r).2 hrq⟩

/-- **定理 4.6**：`CP ⊆ M + I`（只用 A5）。 -/
theorem CP_subset (p q : P) (h : (K.C * K.par) p q) : K.mate p q ∨ q = p := by
  obtain ⟨r, hrp, hrq⟩ := h
  by_cases hqp : q = p
  · exact Or.inr hqp
  · exact Or.inl (K.parents_mate (fun h' => hqp h'.symm) hrp hrq)

/-! ## §5 序关系 -/

/-- **定理 5.1**：`E` 与 `Y` 不相交。 -/
theorem elder_disjoint (p q : P) : ¬ (K.elder p q ∧ K.Y p q) := by
  rintro ⟨h1, h2⟩
  exact K.elder_asymm h1 h2

/-- **定理 5.2**：`EY ⊆ S + I`。 -/
theorem EY_subset (p r : P) (h : (K.elder * K.elder⁻¹) p r) : K.S p r ∨ r = p := by
  obtain ⟨q, hpq, hrq⟩ := h
  by_cases hrp : r = p
  · exact Or.inr hrp
  · refine Or.inl ((K.S_iff p r).2 ⟨fun h' => hrp h'.symm, ?_⟩)
    have hspq : K.S p q := Or.inl hpq
    have hsrq : K.S r q := Or.inl hrq
    obtain ⟨a, hpa⟩ := K.par_nonempty p
    exact ⟨a, hpa, (K.par_eq_of_S hsrq a).2 ((K.par_eq_of_S hspq a).1 hpa)⟩

/-- **定理 5.3**：`YE ⊆ S + I`。 -/
theorem YE_subset (p r : P) (h : (K.elder⁻¹ * K.elder) p r) : K.S p r ∨ r = p := by
  obtain ⟨q, hqp, hqr⟩ := h
  by_cases hrp : r = p
  · exact Or.inr hrp
  · refine Or.inl ((K.S_iff p r).2 ⟨fun h' => hrp h'.symm, ?_⟩)
    have hsqp : K.S q p := Or.inl hqp
    have hsqr : K.S q r := Or.inl hqr
    obtain ⟨a, hqa⟩ := K.par_nonempty q
    exact ⟨a, (K.par_eq_of_S hsqp a).1 hqa, (K.par_eq_of_S hsqr a).1 hqa⟩

end KinCore

/-! ## §2.3 B 组：完备化公理 -/

/-- 完备化公理（B 组）。 -/
structure Complete {P : Type u} (K : KinCore P) : Prop where
  /-- **(B1) 配偶共育**：配偶的子女也是自己的子女。 -/
  mate_coparent : ∀ {p q r : P}, K.mate p q → K.par r p → K.par r q
  /-- **(B2) 人人有子女**。 -/
  child_exists : ∀ p : P, ∃ q : P, K.par q p
  /-- **(B3) 人人有配偶**。 -/
  mate_exists : ∀ p : P, ∃ q : P, K.mate p q
  /-- **(B4) 人人有兄姐**。 -/
  elder_above : ∀ p : P, ∃ q : P, K.elder p q
  /-- **(B5) 人人有弟妹**。 -/
  elder_below : ∀ p : P, ∃ q : P, K.elder q p

namespace Complete

variable {P : Type u} {K : KinCore P}

/-- (B1)+(B2) 给出 (A5) 的逆：配偶必有共同子女。 -/
theorem mate_common (h : Complete K) {p q : P} (hm : K.mate p q) :
    ∃ r, K.par r p ∧ K.par r q := by
  obtain ⟨r, hr⟩ := h.child_exists p
  exact ⟨r, hr, h.mate_coparent hm hr⟩

/-- **定理 6.1**：`CP = M + I`。 -/
theorem CP_eq (h : Complete K) (p q : P) :
    (K.C * K.par) p q ↔ (K.mate + 1) p q := by
  constructor
  · intro hcp
    rcases K.CP_subset p q hcp with hm | hqp
    · exact Or.inl hm
    · exact Or.inr hqp
  · rintro (hm | hqp)
    · obtain ⟨r, hrp, hrq⟩ := h.mate_common hm
      exact ⟨r, hrp, hrq⟩
    · rw [hqp]
      obtain ⟨r, hr⟩ := h.child_exists p
      exact ⟨r, hr, hr⟩

/-- **定理 6.2**：`MC = C`。 -/
theorem MC_eq (h : Complete K) (p r : P) :
    (K.mate * K.C) p r ↔ K.C p r := by
  constructor
  · intro hmc
    obtain ⟨q, hpq, hqr⟩ := hmc
    exact h.mate_coparent (K.mate_symm hpq) hqr
  · intro hpr
    obtain ⟨q, hq⟩ := h.mate_exists p
    exact ⟨q, hq, h.mate_coparent hq hpr⟩

/-- **定理 6.3**：`MM = I`。 -/
theorem MM_eq (h : Complete K) (p q : P) :
    (K.mate * K.mate) p q ↔ q = p := by
  constructor
  · intro hmm
    obtain ⟨s, hps, hsq⟩ := hmm
    exact K.mate_unique hsq (K.mate_symm hps)
  · rintro rfl
    obtain ⟨s, hs⟩ := h.mate_exists q
    exact ⟨s, hs, K.mate_symm hs⟩

/-- **定理 6.4**：`M³ = M`。 -/
theorem M_cube_eq (h : Complete K) : K.mate * K.mate * K.mate = K.mate := by
  have hmm : K.mate * K.mate = 1 := Rel.ext (fun p q => h.MM_eq p q)
  rw [hmm, Rel.one_mul]

/-- `S p r` 且人人有兄姐 ⟹ `p`、`r` 有共同的年长者。 -/
theorem common_elder_of_S (h : Complete K) {p r : P} (hsr : K.S p r) :
    ∃ q, K.elder p q ∧ K.elder r q := by
  obtain ⟨q0, hq0⟩ := h.elder_above p
  have hS : K.S p q0 := Or.inl hq0
  have hpar : ∀ x, K.par q0 x ↔ K.par r x := by
    intro x
    exact ⟨fun hx => (K.par_eq_of_S hsr x).1 ((K.par_eq_of_S hS x).2 hx),
           fun hx => (K.par_eq_of_S hS x).1 ((K.par_eq_of_S hsr x).2 hx)⟩
  by_cases hqr : q0 = r
  · rw [hqr] at hq0
    obtain ⟨q1, hq1⟩ := h.elder_above r
    exact ⟨q1, K.elder_trans hq0 hq1, hq1⟩
  · obtain ⟨a, ha⟩ := K.par_nonempty q0
    have hSq : K.S q0 r := (K.S_iff q0 r).2 ⟨hqr, ⟨a, ha, (hpar a).1 ha⟩⟩
    rcases (K.S_apply q0 r).1 hSq with h' | h'
    · obtain ⟨q1, hq1⟩ := h.elder_above r
      exact ⟨q1, K.elder_trans (K.elder_trans hq0 h') hq1, hq1⟩
    · exact ⟨q0, hq0, h'⟩

/-- `S p r` 且人人有弟妹 ⟹ `p`、`r` 有共同的年轻者。 -/
theorem common_younger_of_S (h : Complete K) {p r : P} (hsr : K.S p r) :
    ∃ q, K.elder q p ∧ K.elder q r := by
  obtain ⟨q0, hq0⟩ := h.elder_below p
  have hS : K.S q0 p := Or.inl hq0
  have hpar : ∀ x, K.par q0 x ↔ K.par r x := by
    intro x
    exact ⟨fun hx => (K.par_eq_of_S hsr x).1 ((K.par_eq_of_S hS x).1 hx),
           fun hx => (K.par_eq_of_S hS x).2 ((K.par_eq_of_S hsr x).2 hx)⟩
  by_cases hqr : q0 = r
  · rw [hqr] at hq0
    obtain ⟨q1, hq1⟩ := h.elder_below r
    exact ⟨q1, K.elder_trans hq1 hq0, hq1⟩
  · obtain ⟨a, ha⟩ := K.par_nonempty q0
    have hSq : K.S q0 r := (K.S_iff q0 r).2 ⟨hqr, ⟨a, ha, (hpar a).1 ha⟩⟩
    rcases (K.S_apply q0 r).1 hSq with h' | h'
    · exact ⟨q0, hq0, h'⟩
    · obtain ⟨q1, hq1⟩ := h.elder_below r
      exact ⟨q1, K.elder_trans (K.elder_trans hq1 h') hq0, hq1⟩

/-- **定理 5.4（⟸）**：`(B4)` ⟹ `EY = S + I`。 -/
theorem EY_eq (h : Complete K) (p r : P) :
    (K.elder * K.elder⁻¹) p r ↔ (K.S + 1) p r := by
  constructor
  · intro hab
    rcases K.EY_subset p r hab with h' | h'
    · exact Or.inl h'
    · exact Or.inr h'
  · intro h'
    rcases h' with hsr | hrp
    · obtain ⟨q, h1, h2⟩ := h.common_elder_of_S hsr
      exact ⟨q, h1, h2⟩
    · rw [hrp]
      obtain ⟨q, hq⟩ := h.elder_above p
      exact ⟨q, hq, hq⟩

/-- **定理 5.5（⟸）**：`(B5)` ⟹ `YE = S + I`。 -/
theorem YE_eq (h : Complete K) (p r : P) :
    (K.elder⁻¹ * K.elder) p r ↔ (K.S + 1) p r := by
  constructor
  · intro hab
    rcases K.YE_subset p r hab with h' | h'
    · exact Or.inl h'
    · exact Or.inr h'
  · intro h'
    rcases h' with hsr | hrp
    · obtain ⟨q, h1, h2⟩ := h.common_younger_of_S hsr
      exact ⟨q, h1, h2⟩
    · rw [hrp]
      obtain ⟨q, hq⟩ := h.elder_below p
      exact ⟨q, hq, hq⟩

/-- **定理 5.4（⟹）**：`EY = S + I` ⟹ `(B4)`。 -/
theorem elderAbove_of_EY
    (h : ∀ p r : P, (K.elder * K.elder⁻¹) p r ↔ (K.S + 1) p r) :
    ∀ p, ∃ q, K.elder p q := by
  intro p
  have hpp : (K.S + 1) p p := Or.inr rfl
  obtain ⟨q, hq, -⟩ := (h p p).2 hpp
  exact ⟨q, hq⟩

/-- **定理 5.5（⟹）**：`YE = S + I` ⟹ `(B5)`。 -/
theorem elderBelow_of_YE
    (h : ∀ p r : P, (K.elder⁻¹ * K.elder) p r ↔ (K.S + 1) p r) :
    ∀ p, ∃ q, K.elder q p := by
  intro p
  have hpp : (K.S + 1) p p := Or.inr rfl
  obtain ⟨q, -, hq⟩ := (h p p).2 hpp
  exact ⟨q, hq⟩

end Complete

end PCMS