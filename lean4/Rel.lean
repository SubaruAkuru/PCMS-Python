/-
# 亲属关系代数（PCMS）—— 基础关系演算

本文件用 Lean 4 核心库（无 Mathlib 依赖）定义亲属关系式。

**设计要点**：亲属关系式 `R` 即 `P` 上的二元关系，写作 `R : Rel P := P → P → Prop`。
原文的 `{R}_p` 与 `p —R→ q` 都直接对应到 `R p q`。

这样做的好处：
* 完全自足，不依赖 Mathlib，任何人下载 Lean 4 + 本仓库即可验证；
* 原文 §1.1 的"`{R}_p` 是 `P` 的关于 `p` 的子集"自动成立（`R p : P → Prop`）；
* 原文 §1.2 的"`R₁ = R₂ ⟺ ∀p, {R₁}_p = {R₂}_p`"就是函数外延性。

运算符全部为**定义**，与原文 §1.2 一致。
-/

namespace PCMS

universe u

/-- 亲属关系式：`P` 上的二元关系。`R p q` 表示「`q` 是 `p` 的 `R`」，
即原文的 `q ∈ {R}_p` 与 `p —R→ q`。 -/
def Rel (P : Type u) : Type u := P → P → Prop

namespace Rel

variable {P : Type u}

/-- 关系外延性：原文「`R₁ = R₂` 当且仅当 `∀p, {R₁}_p = {R₂}_p`」。
在 `Rel P` 中这就是函数外延性。 -/
theorem ext {R₁ R₂ : Rel P} (h : ∀ p q, R₁ p q ↔ R₂ p q) : R₁ = R₂ :=
  funext fun p => funext fun q => propext (h p q)

/-- 加法：`{R₁ + R₂}_p = {R₁}_p ∪ {R₂}_p`。-/
def add (R₁ R₂ : Rel P) : Rel P := fun p q => R₁ p q ∨ R₂ p q
/-- 乘法：`{R₁ R₂}_p = ⋃_{q ∈ {R₁}_p} {R₂}_q`。-/
def mul (R₁ R₂ : Rel P) : Rel P := fun p q => ∃ s, R₁ p s ∧ R₂ s q
/-- 逆：`{R⁻¹}_p = {q | q —R→ p}`。-/
def inv (R : Rel P) : Rel P := fun p q => R q p

instance : Add (Rel P) := ⟨add⟩
instance : Mul (Rel P) := ⟨mul⟩
instance : Inv (Rel P) := ⟨inv⟩
instance : Zero (Rel P) := ⟨fun _ _ => False⟩
instance : One (Rel P) := ⟨fun p q => q = p⟩

@[simp] theorem add_apply (R₁ R₂ : Rel P) (p q : P) : (R₁ + R₂) p q ↔ R₁ p q ∨ R₂ p q :=
  Iff.rfl
@[simp] theorem mul_apply (R₁ R₂ : Rel P) (p q : P) :
    (R₁ * R₂) p q ↔ ∃ s, R₁ p s ∧ R₂ s q := Iff.rfl
@[simp] theorem inv_apply (R : Rel P) (p q : P) : R⁻¹ p q ↔ R q p := Iff.rfl
@[simp] theorem zero_apply (p q : P) : (0 : Rel P) p q ↔ False := Iff.rfl
@[simp] theorem one_apply (p q : P) : (1 : Rel P) p q ↔ q = p := Iff.rfl

/-! ## 关系代数的基本定律（不依赖任何亲属公理） -/

theorem add_comm (R₁ R₂ : Rel P) : R₁ + R₂ = R₂ + R₁ :=
  ext fun p q => by simp [or_comm]

theorem add_assoc (R₁ R₂ R₃ : Rel P) : (R₁ + R₂) + R₃ = R₁ + (R₂ + R₃) :=
  ext fun p q => by simp [or_assoc]

theorem add_zero (R : Rel P) : R + 0 = R :=
  ext fun p q => by simp

theorem zero_add (R : Rel P) : 0 + R = R :=
  ext fun p q => by simp

theorem mul_assoc (R₁ R₂ R₃ : Rel P) : (R₁ * R₂) * R₃ = R₁ * (R₂ * R₃) :=
  ext fun p q => by
    constructor
    · rintro ⟨s, ⟨t, h1, h2⟩, h3⟩
      exact ⟨t, h1, s, h2, h3⟩
    · rintro ⟨t, h1, s, h2, h3⟩
      exact ⟨s, ⟨t, h1, h2⟩, h3⟩

theorem one_mul (R : Rel P) : 1 * R = R :=
  ext fun p q => by
    constructor
    · rintro ⟨s, rfl, h⟩; exact h
    · intro h; exact ⟨p, rfl, h⟩

theorem mul_one (R : Rel P) : R * 1 = R :=
  ext fun p q => by
    constructor
    · rintro ⟨s, h, rfl⟩; exact h
    · intro h; exact ⟨q, h, rfl⟩

theorem zero_mul (R : Rel P) : 0 * R = 0 :=
  ext fun p q => by simp

theorem mul_zero (R : Rel P) : R * 0 = 0 :=
  ext fun p q => by simp

theorem mul_add (R₁ R₂ R₃ : Rel P) : R₁ * (R₂ + R₃) = R₁ * R₂ + R₁ * R₃ :=
  ext fun p q => by
    constructor
    · rintro ⟨s, h1, h2 | h3⟩
      · exact Or.inl ⟨s, h1, h2⟩
      · exact Or.inr ⟨s, h1, h3⟩
    · rintro (⟨s, h1, h2⟩ | ⟨s, h1, h3⟩)
      · exact ⟨s, h1, Or.inl h2⟩
      · exact ⟨s, h1, Or.inr h3⟩

theorem add_mul (R₁ R₂ R₃ : Rel P) : (R₁ + R₂) * R₃ = R₁ * R₃ + R₂ * R₃ :=
  ext fun p q => by
    constructor
    · rintro ⟨s, h1 | h1, h2⟩
      · exact Or.inl ⟨s, h1, h2⟩
      · exact Or.inr ⟨s, h1, h2⟩
    · rintro (⟨s, h1, h2⟩ | ⟨s, h1, h2⟩)
      · exact ⟨s, Or.inl h1, h2⟩
      · exact ⟨s, Or.inr h1, h2⟩

/-! ## 逆运算 -/

theorem inv_inv (R : Rel P) : R⁻¹⁻¹ = R :=
  ext fun p q => by simp

theorem inv_mul (R₁ R₂ : Rel P) : (R₁ * R₂)⁻¹ = R₂⁻¹ * R₁⁻¹ :=
  ext fun p q => by
    constructor
    · rintro ⟨s, h1, h2⟩
      exact ⟨s, h2, h1⟩
    · rintro ⟨s, h1, h2⟩
      exact ⟨s, h2, h1⟩

theorem inv_add (R₁ R₂ : Rel P) : (R₁ + R₂)⁻¹ = R₁⁻¹ + R₂⁻¹ :=
  ext fun p q => by simp

theorem inv_zero : (0 : Rel P)⁻¹ = 0 := ext fun p q => by simp

theorem inv_one : (1 : Rel P)⁻¹ = 1 := ext fun p q => by simp [eq_comm]

theorem inv_congr {R₁ R₂ : Rel P} (h : R₁ = R₂) : R₁⁻¹ = R₂⁻¹ := by rw [h]

/-- 逆运算一般并非对合地反序（原文 §1.2 第 (2) 条 `(R^a)^b = R^{ab}` 需要特别讨论）。 -/
theorem inv_inv_mul (R₁ R₂ : Rel P) : (R₁ * R₂)⁻¹⁻¹ = R₁ * R₂ := inv_inv _

end Rel

end PCMS
