/-
# 十三条公理（平铺编号）

与 `AXIOMS.md` 的 A/B 分组等价，但把两组打散成 13 条**地位平等**的公理，
编号 `公理1` … `公理13`，字段名 `ax1` … `ax13`。

本文件不重做证明：它把 13 条公理拆装回 `KinCore`（8 条）与 `Complete`（5 条）
两个结构体，于是 `Core.lean` 中已有的全部定理直接适用。这样既保持了平铺编号，
又不必重复几百行证明。
-/

import Combined

namespace PCMS

universe u

/-- 十三条公理。 -/
structure Kin13 (P : Type u) where
  /-- 父母关系。 -/
  par : Rel P
  /-- 配偶关系。 -/
  mate : Rel P
  /-- 兄姐关系。 -/
  elder : Rel P
  /-- **公理1（双亲性）** 每人至少两个互不相同的父母。 -/
  ax1 : ∀ p : P, ∃ a b : P, a ≠ b ∧ par p a ∧ par p b
  /-- **公理2（配偶对称）**。 -/
  ax2 : ∀ {p q : P}, mate p q → mate q p
  /-- **公理3（配偶唯一）**。 -/
  ax3 : ∀ {p q r : P}, mate p q → mate p r → q = r
  /-- **公理4（无自婚）**。 -/
  ax4 : ∀ p : P, ¬ mate p p
  /-- **公理5（共子即配）** 有共同子女的两人互为配偶。 -/
  ax5 : ∀ {p q r : P}, p ≠ q → par r p → par r q → mate p q
  /-- **公理6（配偶共育）** 配偶的子女也是自己的子女。 -/
  ax6 : ∀ {p q r : P}, mate p q → par r p → par r q
  /-- **公理7（同胞即共父母）**。 -/
  ax7 : ∀ {p q : P}, (elder p q ∨ elder q p) ↔
    (p ≠ q ∧ ∃ r : P, par p r ∧ par q r)
  /-- **公理8（同胞足数）** 每人至少两个同胞。 -/
  ax8 : ∀ p : P, ∃ a b : P, a ≠ b ∧ (elder p a ∨ elder a p) ∧
    (elder p b ∨ elder b p)
  /-- **公理9（长幼传递）**。 -/
  ax9 : ∀ {p q r : P}, elder p q → elder q r → elder p r
  /-- **公理10（人人有兄姐）**。 -/
  ax10 : ∀ p : P, ∃ q : P, elder p q
  /-- **公理11（人人有弟妹）**。 -/
  ax11 : ∀ p : P, ∃ q : P, elder q p
  /-- **公理12（人人有子女）**。 -/
  ax12 : ∀ p : P, ∃ q : P, par q p
  /-- **公理13（人人有配偶）**。 -/
  ax13 : ∀ p : P, ∃ q : P, mate p q

namespace Kin13

variable {P : Type u} (K : Kin13 P)

/-- 前八条公理给出结构层。 -/
def toCore : KinCore P where
  par := K.par
  mate := K.mate
  elder := K.elder
  two_parents := K.ax1
  mate_symm := K.ax2
  mate_unique := K.ax3
  mate_irrefl := K.ax4
  mate_of_coparent := K.ax5
  sib_iff := K.ax7
  elder_trans := K.ax9
  sib_two := K.ax8

/-- 后五条公理给出完备化层。 -/
theorem complete : Complete K.toCore where
  mate_coparent := K.ax6
  child_exists := K.ax12
  mate_exists := K.ax13
  elder_above := K.ax10
  elder_below := K.ax11

/-! ## 摘要定理（全部由 `Core.lean` 直接搬来） -/

/-- 子女 `C := P⁻¹`。 -/
def C : Rel P := K.toCore.C

/-- 弟妹 `Y := E⁻¹`。 -/
def Y : Rel P := K.toCore.Y

/-- 兄弟姐妹 `S := E + Y`。 -/
def S : Rel P := K.toCore.S

/-- 定理：每人恰有两个父母。 -/
theorem exactly_two_parents (p : P) : ∃ a b : P, a ≠ b ∧ K.par p a ∧ K.par p b ∧
    ∀ c : P, K.par p c → c = a ∨ c = b := by
  obtain ⟨a, b, hab, ha, hb⟩ := K.ax1 p
  exact ⟨a, b, hab, ha, hb, fun c hc => K.toCore.par_cases hab ha hb hc⟩

/-- 定理：全同胞——同胞的父母完全相同。 -/
theorem sib_full {p q : P} (h : K.S p q) : ∀ r, K.par p r ↔ K.par q r :=
  K.toCore.par_eq_of_S h

/-- 定理：长幼反自反。 -/
theorem not_elder_self (p : P) : ¬ K.elder p p :=
  K.toCore.not_elder_self p

/-- 定理：长幼反对称。 -/
theorem elder_asymm {p q : P} (h : K.elder p q) : ¬ K.elder q p :=
  K.toCore.elder_asymm h

/-- 定理：`PC = S + I`。 -/
theorem PC_eq (p r : P) : (K.par * K.C) p r ↔ (K.S + 1) p r :=
  K.toCore.PC_eq p r

/-- 定理：`SS = S + I`。 -/
theorem SS_eq (p r : P) : (K.S * K.S) p r ↔ (K.S + 1) p r :=
  K.toCore.SS_eq p r

/-- 定理：`PM = P`。 -/
theorem PM_eq (p r : P) : (K.par * K.mate) p r ↔ K.par p r :=
  K.toCore.PM_eq p r

/-- 定理：`SP = P`。 -/
theorem SP_eq (p r : P) : (K.S * K.par) p r ↔ K.par p r :=
  K.toCore.SP_eq p r

/-- 定理：`CS = C`。 -/
theorem CS_eq (p r : P) : (K.C * K.S) p r ↔ K.C p r :=
  K.toCore.CS_eq p r

/-- 定理：`CP = M + I`。 -/
theorem CP_eq (p q : P) : (K.C * K.par) p q ↔ (K.mate + 1) p q :=
  K.complete.CP_eq p q

/-- 定理：`MC = C`。 -/
theorem MC_eq (p r : P) : (K.mate * K.C) p r ↔ K.C p r :=
  K.complete.MC_eq p r

/-- 定理：`MM = I`。 -/
theorem MM_eq (p q : P) : (K.mate * K.mate) p q ↔ q = p :=
  K.complete.MM_eq p q

/-- 定理：`M³ = M`。 -/
theorem M_cube_eq : K.mate * K.mate * K.mate = K.mate :=
  K.complete.M_cube_eq

/-- 定理：`EY = S + I`。 -/
theorem EY_eq (p r : P) : (K.elder * K.elder⁻¹) p r ↔ (K.S + 1) p r :=
  K.complete.EY_eq p r

/-- 定理：`YE = S + I`。 -/
theorem YE_eq (p r : P) : (K.elder⁻¹ * K.elder) p r ↔ (K.S + 1) p r :=
  K.complete.YE_eq p r

/-- 定理：同胞对称。 -/
theorem S_symm (p q : P) : K.S p q ↔ K.S q p :=
  K.toCore.S_symm p q

/-- 定理：同胞类上长幼是严格全序（完全性 + 唯一性）。 -/
theorem elder_total {p q : P} (h : K.S p q) :
    (K.elder p q ∨ K.elder q p) ∧ ¬ (K.elder p q ∧ K.elder q p) :=
  K.toCore.elder_strict_total h

/-- 定理：配偶在父母角色上可互换。 -/
theorem mate_par_iff {p q : P} (hm : K.mate p q) :
    ∀ r, K.par r p ↔ K.par r q :=
  K.complete.mate_par_iff hm

/-- 定理：配偶 ⇔ 有共同子女（`p ≠ q`）。 -/
theorem mate_iff_common_child {p q : P} (hpq : p ≠ q) :
    K.mate p q ↔ ∃ r, K.par r p ∧ K.par r q :=
  K.complete.mate_iff_common_child hpq

end Kin13

end PCMS
