/-
# 汇总：本形式化已验证的全部结果

本文件不新增数学内容，只把所有主要结论 `#check` 一遍，作为"验证清单"。
运行 `lean Main.lean` 且输出无 error，即表示以下定理全部机器验证通过。
-/

import Rel
import Kin
import Identities
import Order
import Model
import Coupled
import Unbounded
import ModelZ

/-! ## 0. 关系代数（无需任何亲属公理，§2） -/

#check @PCMS.Rel.add_comm
#check @PCMS.Rel.add_assoc
#check @PCMS.Rel.mul_assoc
#check @PCMS.Rel.one_mul
#check @PCMS.Rel.mul_one
#check @PCMS.Rel.zero_mul
#check @PCMS.Rel.mul_zero
#check @PCMS.Rel.mul_add
#check @PCMS.Rel.add_mul
#check @PCMS.Rel.inv_inv
#check @PCMS.Rel.inv_mul
#check @PCMS.Rel.inv_add
#check @PCMS.Rel.inv_zero
#check @PCMS.Rel.inv_one

/-! ## 1. 公理的语义结构（§1.1） -/

#check @PCMS.Kin
#check @PCMS.Kin.S_iff_common

/-! ## 2. 由 (A3)P+(A5)+(A6) 导出的强约束 -/

-- 每人至多两个父母。
#check @PCMS.Kin.par_unique
-- 给定一个父母可以找到另一个。
#check @PCMS.Kin.par_exists_second
-- 两个不同父母互为配偶。
#check @PCMS.Kin.parents_mate
-- 每人恰有两个父母（分类形式）。
#check @PCMS.Kin.par_cases
-- 全同胞定理。
#check @PCMS.Kin.par_eq_of_sib'
-- 兄弟姐妹的父母相同。
#check @PCMS.Kin.par_eq_of_S

/-! ## 3. §1.3 的简化等式 -/

-- ① `PC = S + I`
#check @PCMS.Kin.PC_eq
-- ① `SS = S + I`
#check @PCMS.Kin.SS_eq
-- ② `PM = P`
#check @PCMS.Kin.PM_eq
-- ② `SP = P`
#check @PCMS.Kin.SP_eq
-- ③ `CP ⊆ M + I`
#check @PCMS.Kin.CP_subset
-- ④ `CS = C`
#check @PCMS.Kin.CS_eq

/-! ## 4. §1.5 `EY` 的真实情况 -/

-- `E + Y = S` 是定义
#check @PCMS.Kin.E_add_Y
-- `EY ⊆ S + I`
#check @PCMS.Kin.EY_subset
-- `YE ⊆ S + I`
#check @PCMS.Kin.YE_subset
-- `E` 与 `Y` 不相交
#check @PCMS.Kin.elder_disjoint

/-! ## 5. 相容性模型（§1.1 的模型存在性） -/

-- 逐条验证过的亲属树
#check @PCMS.Model.kin
-- 该模型满足全部公理
#check @PCMS.Model.par_two
#check @PCMS.Model.mate_of_common_child
#check @PCMS.Model.mate_unique
#check @PCMS.Model.elder_sib
#check @PCMS.Model.sib_common_parent
#check @PCMS.Model.sib_two

-- 但 `EY ≠ S`：原文 `EY = E + I + Y` 不成立
#check @PCMS.Model.EY_ne_S
-- 更强：`EY ≠ S + I`
#check @PCMS.Model.EY_ne_S_add_I

/-! ## 6. 补全公理 (A9)(A10)(A11) 之后的完整等式 -/

#check @PCMS.Coupled
-- (A11) 推出配偶对称
#check @PCMS.Coupled.mate_symm
-- (A5) 的逆命题
#check @PCMS.Coupled.mate_common_child
-- ⑤ `MM = I`
#check @PCMS.Coupled.MM_eq
-- ③ `CP = M + I`
#check @PCMS.Coupled.CP_eq
-- ④ `MC = C`
#check @PCMS.Coupled.MC_eq
-- M³ = M（原文 §1.5 用到）
#check @PCMS.Coupled.M_cube_eq

/-! ## 7. 使 EY = YE = S + I 与 CP = M + I 成立的精确条件 -/

-- (A3a) 人人有兄姐
#check @PCMS.ElderAbove
-- (A3a′) 人人有弟妹
#check @PCMS.ElderBelow
-- ElderAbove ⟹ EY = S + I
#check @PCMS.Kin.EY_eq
-- ElderBelow ⟹ YE = S + I
#check @PCMS.Kin.YE_eq
-- 反向：EY = S + I ⟹ ElderAbove（故公理不可减弱）
#check @PCMS.Kin.elderAbove_of_EY
-- 反向：YE = S + I ⟹ ElderBelow
#check @PCMS.Kin.elderBelow_of_YE
-- S p r 时共同长辈/晚辈的构造
#check @PCMS.Kin.common_elder_of_S
#check @PCMS.Kin.common_younger_of_S

-- (A8) 配偶必有共同子女
#check @PCMS.MateCommonChild
-- (A9) 人人有子女
#check @PCMS.ChildExists
-- (A8)+(A9) ⟹ CP = M + I
#check @PCMS.Kin.CP_eq
-- 反向：CP = M + I ⟹ (A9)
#check @PCMS.Kin.childExists_of_CP
-- 反向：CP = M + I ⟹ (A8)
#check @PCMS.Kin.mateCommonChild_of_CP

/-! ## 8. 相容性：(A3a)+(A3a′) 与原公理并存 -/

-- ℤ 索引的模型（兄弟类双向无限）
#check @PCMS.ModelZ.kin
#check @PCMS.ModelZ.elderAbove
#check @PCMS.ModelZ.elderBelow
-- 该模型中 EY = S + I 与 YE = S + I 均成立
#check @PCMS.ModelZ.EY_holds
#check @PCMS.ModelZ.YE_holds