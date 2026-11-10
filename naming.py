# -*- coding: utf-8 -*-
"""
naming.py —— 基于 kinship_formula 亲属关系引擎的中文呼称命名脚本。

设计目标：
1. 异性婚姻：命名结果尽可能拟合 `python3-relationship` 库（mumuy/relationship 的
   Python 移植版）的输出。由于该库本质上是"关系链 → 称谓表"的查表实现，命名并非
   完全规则化，因此拟合目标是"语义正确 + 尽量命中库内词表"，而非逐条一致。
2. 同性婚姻：relationship 库在 selector 中显式剔除了同性婚姻链
   （见 selector.py 中"同志关系去除"的正则），本脚本按"性别本位 + 类推"原则外推
   命名，使 kinship_formula 引擎（性别自由，天然支持同性婚姻）的每一条链都能得到
   一个合乎语感的呼称。
3. 扩展命名：库无法命名但实际可命名的关系（继父/继母/继子/继女、超过 12 代的
   世祖/世孙、同性姻亲、旁系深处等）。

详细规则见《命名规则.md》。

公共接口：
    naming(formula)         KinMonomial -> str（主呼称）；KinPolynomial -> list[str]
    naming_full(formula)    同上，但返回 {主呼称, 备选呼称, 单项式} 的结构
    name_chain(gens)        从原始生成元链计算关系并命名，附带同性婚姻/继亲标注

生成元约定（来自 generators.py / kinship_formula.py）：
    Parent('m')=父  Parent('f')=母  Child('m')=子  Child('f')=女
    Mate('m')=夫   Mate('f')=妻   Elder('m')=兄 Elder('f')=姐
    Younger('m')=弟 Younger('f')=妹  Identity=自己  Zero=无
"""

from generators import Parent, Child, Mate, Elder, Younger, Identity, Zero
from kinship_formula import KinMonomial, KinPolynomial, init, kinship_type, priority

# ----------------------------------------------------------------------------
# 基础称谓表
# ----------------------------------------------------------------------------

MALE, FEMALE = 'm', 'f'

PARENT = {MALE: '爸爸', FEMALE: '妈妈'}
PARENT_ALTS = {MALE: ['父亲', '爸', '父'], FEMALE: ['母亲', '妈', '母']}

CHILD = {MALE: '儿子', FEMALE: '女儿'}
CHILD_ALTS = {MALE: ['儿', '子'], FEMALE: ['女']}

SIB = {'E': {MALE: '哥哥', FEMALE: '姐姐'}, 'Y': {MALE: '弟弟', FEMALE: '妹妹'}}
SIB_F = {'E': {MALE: '兄', FEMALE: '姊'}, 'Y': {MALE: '弟', FEMALE: '妹'}}
SIB_ALTS = {'E': {MALE: ['哥', '兄长'], FEMALE: ['姐', '姊']},
            'Y': {MALE: ['弟'], FEMALE: ['妹']}}

SPOUSE = {MALE: '丈夫', FEMALE: '妻子'}
SPOUSE_ALTS = {MALE: ['老公', '夫', '先生'], FEMALE: ['老婆', '妻', '太太']}

# 直系祖辈/晚辈的世代前缀：只保留"曾"（曾祖父母、曾外祖父母、外曾祖父母、
# 外曾外祖父母保留；"高、天、烈、太、远、鼻"与"玄、来、晜、仍、云、耳"等为
# 现代拟构，不采用）。更深世代用"曾/外曾"长链直接写出：
#   4 代 = 曾曾祖父/曾曾外祖父…；5 代 = 曾曾曾祖父…（外 按母/女链交叉插入）


def _alt_combine(primary, alts):
    """把主呼称并入备选列表返回（去重保序）。"""
    out = []
    for x in [primary] + list(alts or []):
        if x and x not in out:
            out.append(x)
    return out


# ----------------------------------------------------------------------------
# 直系祖辈：全 Parent 链
# ----------------------------------------------------------------------------

def _formal_descendant(gs):
    """直系晚辈的正式词形（子/女/孙/孙女/外孙/外孙女/曾孙…），用于组合。"""
    if len(gs) == 1:
        return '子' if gs[0] == MALE else '女'
    if len(gs) == 2:
        if gs[0] == MALE:
            return '孙' if gs[1] == MALE else '孙女'
        return '外孙' if gs[1] == MALE else '外孙女'
    prim, _ = name_descendants(list(gs))
    return prim


def _formal_descendant_at(gen, gender):
    """目标在绝对辈分 gen（gen <= -2）时的通用孙辈词（孙/孙女/曾孙…）。

    只负责“辈分 + 性别”这一层；支系（外/堂表/眷姻）由段前缀负责。
    用于重锚名的负辈分兜底，避免把 -2、-3 代目标错写成“父/母/孙”等。
    """
    if gen > -2:
        raise ValueError('_formal_descendant_at expects gen <= -2')
    return _formal_descendant([MALE] * (-gen - 1) + [gender])


def _formal_descendant_seq_at(gen, seq):
    """按目标绝对辈分 gen 截取/补齐性别序列，保留 Y 链里的“外”信息。"""
    if gen > -2:
        raise ValueError('_formal_descendant_seq_at expects gen <= -2')
    need = -gen
    if len(seq) < need:
        seq = [MALE] * (need - len(seq)) + list(seq)
    else:
        seq = list(seq[-need:])
    return _formal_descendant(seq)


def _term_at_generation(gen, gender):
    """绝对辈分 gen、性别 gender 的通用呼称（不含支系/眷姻前缀）。

    用于兜底：只要辈分与性别正确，段前缀再补支系信息。
    """
    if gen == 0:
        return '兄弟' if gender == MALE else '姊妹'
    if gen == -1:
        return '男' if gender == MALE else '女'
    if gen <= -2:
        return _formal_descendant_at(gen, gender)
    return _formal_ancestor([MALE] * (gen - 1) + [gender])

def name_ancestors(gs):
    """gs: 自"我"向上的性别序列（'m' 父 / 'f' 母）。返回 (主呼称, 备选列表)。

    规则（无碰撞、可任意加长）：
      n=1：爸爸/妈妈；n=2：祖父/祖母/外祖父/外祖母。
      n>=3：自"我"侧逐代剥离——父链加前缀"曾"，母链加前缀"外曾"，
            剥到剩两代时接 祖父/祖母/外祖父/外祖母。
      例：P^5mmfmf（父父母父母）= 曾 + 外曾 + 曾 + 祖母 = 曾外曾曾祖母；
          P^5mmffm（父父母母父）= 曾 + 外曾 + 外曾 + 外祖父 = 曾外曾外曾外祖父。
    """
    n = len(gs)
    if n == 1:
        return PARENT[gs[0]], PARENT_ALTS[gs[0]]
    if n == 2:
        return {(MALE, MALE): ('爷爷', ['祖父']),
                (MALE, FEMALE): ('奶奶', ['祖母']),
                (FEMALE, MALE): ('外公', ['外祖父']),
                (FEMALE, FEMALE): ('外婆', ['外祖母'])}[(gs[0], gs[1])]
    pref = ''
    rest = list(gs)
    while len(rest) > 2:
        pref += '曾' if rest[0] == MALE else '外曾'
        rest = rest[1:]
    base = {(MALE, MALE): '祖父', (MALE, FEMALE): '祖母',
            (FEMALE, MALE): '外祖父', (FEMALE, FEMALE): '外祖母'}[(rest[0], rest[1])]
    return pref + base, []


# ----------------------------------------------------------------------------
# 直系晚辈：全 Child 链
# ----------------------------------------------------------------------------

def name_descendants(gs):
    """gs: 自"我"向下的性别序列（'m' 子 / 'f' 女）。返回 (主呼称, 备选列表)。

    规则（无碰撞、可任意加长）：
      n=1：儿子/女儿；n=2：孙子/孙女/外孙/外孙女。
      n>=3：自"我"侧逐代剥离——子链加前缀"曾"，女链加前缀"外曾"，
            剥到剩两代时接 孙/孙女/外孙/外孙女（末尾不再加"子"）。
      例：C^5mmfmm（子子女子子）= 曾 + 外曾 + 曾 + 孙 = 曾外曾曾孙；
          C^5mmffm（子子女女子）= 曾 + 外曾 + 外曾 + 外孙 = 曾外曾外曾外孙。
    """
    n = len(gs)
    if n == 1:
        return CHILD[gs[0]], CHILD_ALTS[gs[0]]
    if n == 2:
        if gs[0] == MALE:
            return ('孙子' if gs[1] == MALE else '孙女'), []
        return ('外孙' if gs[1] == MALE else '外孙女'), []
    pref = ''
    rest = list(gs)
    while len(rest) > 2:
        pref += '曾' if rest[0] == MALE else '外曾'
        rest = rest[1:]
    base = ('孙' if rest[0] == MALE else '外孙') + ('' if rest[1] == MALE else '女')
    return pref + base, []


# ----------------------------------------------------------------------------
# 旁系（不含配偶）：P^k E/Y C^j 与 E/Y C^j
# ----------------------------------------------------------------------------

# 父/母之兄弟姐妹：P^1 E/Y
UNCLE1 = {
    (MALE, 'E', MALE): '伯父', (MALE, 'Y', MALE): '叔叔',
    (MALE, 'E', FEMALE): '大姑', (MALE, 'Y', FEMALE): '小姑',
    (FEMALE, 'E', MALE): '大舅', (FEMALE, 'Y', MALE): '小舅',
    (FEMALE, 'E', FEMALE): '大姨', (FEMALE, 'Y', FEMALE): '小姨',
}

# 祖辈之兄弟姐妹：P^2 E/Y
UNCLE2 = {
    (MALE, MALE, 'E', MALE): '伯公', (MALE, MALE, 'Y', MALE): '叔公',
    (MALE, MALE, 'E', FEMALE): '姑奶奶', (MALE, MALE, 'Y', FEMALE): '姑奶奶',
    (MALE, FEMALE, 'E', MALE): '大舅爷', (MALE, FEMALE, 'Y', MALE): '小舅爷',
    (MALE, FEMALE, 'E', FEMALE): '姨奶奶', (MALE, FEMALE, 'Y', FEMALE): '姨奶奶',
    (FEMALE, MALE, 'E', MALE): '伯外公', (FEMALE, MALE, 'Y', MALE): '叔外公',
    (FEMALE, MALE, 'E', FEMALE): '姑外婆', (FEMALE, MALE, 'Y', FEMALE): '姑外婆',
    (FEMALE, FEMALE, 'E', MALE): '舅外公', (FEMALE, FEMALE, 'Y', MALE): '舅外公',
    (FEMALE, FEMALE, 'E', FEMALE): '姨外婆', (FEMALE, FEMALE, 'Y', FEMALE): '姨外婆',
}

# 伯叔姑舅姨之配偶（P^1 E/Y M）
UNCLE1_MATE = {
    (MALE, 'E', MALE): {FEMALE: ('伯母', []), MALE: ('伯婿', [])},
    (MALE, 'Y', MALE): {FEMALE: ('婶婶', ['叔母']), MALE: ('叔婿', [])},
    (MALE, 'E', FEMALE): {MALE: ('大姑丈', ['姑丈', '姑父']), FEMALE: ('大姑媳', ['姑媳'])},
    (MALE, 'Y', FEMALE): {MALE: ('小姑丈', ['姑丈', '姑父']), FEMALE: ('小姑媳', ['姑媳'])},
    (FEMALE, 'E', MALE): {FEMALE: ('大舅妈', ['舅妈', '舅母']), MALE: ('大舅婿', ['舅婿'])},
    (FEMALE, 'Y', MALE): {FEMALE: ('小舅妈', ['舅妈', '舅母']), MALE: ('小舅婿', ['舅婿'])},
    (FEMALE, 'E', FEMALE): {MALE: ('大姨丈', ['姨丈', '姨父']), FEMALE: ('大姨媳', ['姨媳'])},
    (FEMALE, 'Y', FEMALE): {MALE: ('小姨丈', ['姨丈', '姨父']), FEMALE: ('小姨媳', ['姨媳'])},
}

# 祖辈之兄弟姐妹的配偶（P^2 E/Y M，异性）
UNCLE2_MATE = {
    (MALE, MALE, 'E', MALE): {FEMALE: '伯婆'}, (MALE, MALE, 'Y', MALE): {FEMALE: '叔婆'},
    (MALE, MALE, 'E', FEMALE): {MALE: '姑爷爷'}, (MALE, MALE, 'Y', FEMALE): {MALE: '姑爷爷'},
    (MALE, FEMALE, 'E', MALE): {FEMALE: '大舅婆'}, (MALE, FEMALE, 'Y', MALE): {FEMALE: '小舅婆'},
    (MALE, FEMALE, 'E', FEMALE): {MALE: '姨爷爷'}, (MALE, FEMALE, 'Y', FEMALE): {MALE: '姨爷爷'},
    (FEMALE, MALE, 'E', MALE): {FEMALE: '伯外婆'}, (FEMALE, MALE, 'Y', MALE): {FEMALE: '叔外婆'},
    (FEMALE, MALE, 'E', FEMALE): {MALE: '姑外公'}, (FEMALE, MALE, 'Y', FEMALE): {MALE: '姑外公'},
    (FEMALE, FEMALE, 'E', MALE): {FEMALE: '舅外婆'}, (FEMALE, FEMALE, 'Y', MALE): {FEMALE: '舅外婆'},
    (FEMALE, FEMALE, 'E', FEMALE): {MALE: '姨外公'}, (FEMALE, FEMALE, 'Y', FEMALE): {MALE: '姨外公'},
}

# k=2（祖辈旁系的子女）线前缀与词形：COUSIN2 键 (g1,g2,eyg)
COUSIN2_LINE = {
    (MALE, MALE, MALE): '堂', (MALE, MALE, FEMALE): '姑表',
    (MALE, FEMALE, MALE): '舅表', (MALE, FEMALE, FEMALE): '姨',
    (FEMALE, MALE, MALE): '堂', (FEMALE, MALE, FEMALE): '姑表',
    (FEMALE, FEMALE, MALE): '舅表', (FEMALE, FEMALE, FEMALE): '姨',
}
# k=2 时"父/母之堂表兄弟/姐妹"（j=1）的具体词形（男：伯/叔…；女：姑母/姨母…）
COUSIN2_MALE = {
    (MALE, MALE, MALE): ('堂伯', '堂叔'), (MALE, MALE, FEMALE): ('姑表伯父', '姑表叔父'),
    (MALE, FEMALE, MALE): ('舅表伯父', '舅表叔父'), (MALE, FEMALE, FEMALE): ('姨伯父', '姨叔父'),
    (FEMALE, MALE, MALE): ('堂舅', '堂舅'), (FEMALE, MALE, FEMALE): ('姑表舅父', '姑表舅父'),
    (FEMALE, FEMALE, MALE): ('舅表舅父', '舅表舅父'), (FEMALE, FEMALE, FEMALE): ('姨舅父', '姨舅父'),
}
COUSIN2_FEMALE = {
    (MALE, MALE, MALE): ('堂姑', '堂姑'), (MALE, MALE, FEMALE): ('姑表姑母', '姑表姑母'),
    (MALE, FEMALE, MALE): ('舅表姑母', '舅表姑母'), (MALE, FEMALE, FEMALE): ('姨姑母', '姨姑母'),
    (FEMALE, MALE, MALE): ('堂姨', '堂姨'), (FEMALE, MALE, FEMALE): ('姑表姨母', '姑表姨母'),
    (FEMALE, FEMALE, MALE): ('舅表姨母', '舅表姨母'), (FEMALE, FEMALE, FEMALE): ('姨姨母', '姨姨母'),
}
# k=2 时与我同辈的表亲（j=2+）类前缀：键 (g1,g2,eyg,cg)
K2_L0_CLASS = {
    (MALE, MALE, MALE, MALE): '从堂', (MALE, MALE, MALE, FEMALE): '堂姑表',
    (MALE, MALE, FEMALE, MALE): '姑表叔表', (MALE, MALE, FEMALE, FEMALE): '姑表姑表',
    (MALE, FEMALE, MALE, MALE): '舅表叔表', (MALE, FEMALE, MALE, FEMALE): '舅表姑表',
    (MALE, FEMALE, FEMALE, MALE): '从母叔表', (MALE, FEMALE, FEMALE, FEMALE): '从母姑表',
    (FEMALE, MALE, MALE, MALE): '堂舅表', (FEMALE, MALE, MALE, FEMALE): '堂姨表',
    (FEMALE, MALE, FEMALE, MALE): '姑表舅表', (FEMALE, MALE, FEMALE, FEMALE): '姑表姨表',
    (FEMALE, FEMALE, MALE, MALE): '舅表舅表', (FEMALE, FEMALE, MALE, FEMALE): '舅表姨表',
    (FEMALE, FEMALE, FEMALE, MALE): '从母舅表', (FEMALE, FEMALE, FEMALE, FEMALE): '再从母',
}


def name_cousin_line(pp, ey, eyg, rest):
    """P^k E/Y C^j：叔伯姑舅姨的子女及更远支系。rest: C 链。"""
    k = len(pp)
    j = len(rest)
    cg = rest[-1].gender
    r = j - k                      # 相对代数：0=与我同辈的堂表亲
    # ---- k == 1：父/母之兄弟姐妹的子女（我的堂表亲）----
    if k == 1:
        if eyg == MALE and pp[0].gender == MALE:
            cls = '堂'
        elif eyg == FEMALE and pp[0].gender == MALE:
            cls = '姑表'
        elif eyg == MALE:
            cls = '舅表'
        else:
            cls = '姨'
        if r == 0:
            return _junior_role_name(0, cg, cls)
        # r>=1：堂表亲的子女（堂侄/堂外甥/堂侄孙/堂甥孙…，按首个子女性别取侄/甥）
        if j == 2:
            if rest[0].gender == FEMALE:
                return cls + '外甥' + ('' if cg == MALE else '女'), \
                    [cls + '甥' + ('男' if cg == MALE else '女')]
            return cls + '侄' + ('' if cg == MALE else '女'), [cls + '侄男']
        stem = '甥' if rest[0].gender == FEMALE else '侄'
        if j == 3:
            des = _formal_descendant([g.gender for g in rest[1:]])
            return cls + stem + des, [cls + stem + des + '男'] if cg == MALE else []
        des = _formal_descendant([g.gender for g in rest[1:]])
        if rest[0].gender == MALE:
            return cls + des, []          # j>=4 库词形省略"侄"（堂曾孙）
        return cls + '甥' + des, []
    # ---- k == 2 ----
    if k == 2:
        key = (pp[0].gender, pp[1].gender, eyg)
        if j == 1:
            if cg == MALE:
                a, b = COUSIN2_MALE[key]
                return a, [b]
            a, b = COUSIN2_FEMALE[key]
            return a, [b]
        if j == 2:
            cls = K2_L0_CLASS[(pp[0].gender, pp[1].gender, eyg, rest[0].gender)]
            return _junior_role_name(0, cg, cls)
        # j>=3：表亲的侄孙辈（从堂侄孙/从堂侄曾孙…）
        cls = K2_L0_CLASS[(pp[0].gender, pp[1].gender, eyg, rest[0].gender)]
        if j == 3:
            return cls + ('侄' if cg == MALE else '侄女'), \
                [cls + '侄男'] if cg == MALE else []
        des = _formal_descendant([g.gender for g in rest[2:]])
        return cls + '侄' + des, []
    # ---- k >= 3 且 j == 1：库词形 = 线1（最近祖先×旁系性别）+ 线2（次近祖先×C性别）+ 祖辈基 ----
    if k >= 3 and j == 1:
        line1 = {(MALE, MALE): '堂', (MALE, FEMALE): '姑表',
                 (FEMALE, MALE): '舅表', (FEMALE, FEMALE): '姨'}[(pp[-1].gender, eyg)]
        outer = '外' if pp[0].gender == FEMALE else ''
        if k == 3:
            base = outer + ('祖父' if cg == MALE else '祖母')
        elif k == 4:
            base = outer + ('曾祖父' if cg == MALE else '曾祖母')
        else:
            base = outer + _formal_ancestor([MALE] * (k - 1))[:-1] + ('父' if cg == MALE else '母')
        if cg == MALE and pp[-2].gender == MALE:
            return line1 + '伯叔' + base, [line1 + '伯' + base, line1 + '叔' + base]
        if cg == MALE:
            line2 = '舅' if pp[-2].gender == FEMALE else '伯叔'
        else:
            line2 = '姨' if pp[-2].gender == FEMALE else '姑'
        return line1 + line2 + base, []
    # ---- k >= 3 且 j >= 2（含"外"或女性旁系）：线1×线2'链 + 角色 ----
    # 库的通用构词法：线1（最近祖先×旁系性别）+ 每代一个线2'（上一代×本代性别）
    # + 角色（由次近祖先×末代性别决定，父/祖父…由世代决定）
    if not all(g.gender == MALE for g in pp) or eyg == FEMALE:
        LINE1 = {(MALE, MALE): '堂', (MALE, FEMALE): '姑表',
                 (FEMALE, MALE): '舅表', (FEMALE, FEMALE): '从母'}
        LINE2 = {(MALE, MALE): '叔表', (MALE, FEMALE): '姑表',
                 (FEMALE, MALE): '舅表', (FEMALE, FEMALE): '姨表'}
        ROLE2 = {(MALE, MALE): '伯叔', (MALE, FEMALE): '姑',
                 (FEMALE, MALE): '舅', (FEMALE, FEMALE): '姨'}
        cls = LINE1[(pp[-1].gender, eyg)] + LINE2[(pp[-2].gender, rest[0].gender)]
        for d in range(2, j):
            cls += LINE2[(rest[d - 2].gender, rest[d - 1].gender)]
        r = j - k
        if r == 0:
            return _junior_role_name(0, cg, cls)
        if r == -1:
            role = ROLE2[(pp[-2].gender, cg)] + ('父' if cg == MALE else '母')
            if cg == MALE and pp[-2].gender == MALE:
                return cls + role, [cls + '伯父', cls + '叔父']
            return cls + role, []
        if r <= -2:
            lv = _formal_ancestor([MALE] * (-r))[:-1]   # 祖父→祖、曾祖父→曾祖…
            role = ROLE2[(pp[-2].gender, cg)] + lv + ('父' if cg == MALE else '母')
            if cg == MALE and pp[-2].gender == MALE:
                return cls + role, [cls + '伯' + lv + '父', cls + '叔' + lv + '父']
            return cls + role, []
        if r == 1:
            return cls + ('侄' if cg == MALE else '侄女'), \
                [cls + '侄男'] if cg == MALE else []
        if r == 2:
            return cls + ('侄孙' if cg == MALE else '侄孙女'), \
                [cls + '侄孙男'] if cg == MALE else []
        des = _formal_descendant([MALE] * (r - 1) + [cg])
        return cls + '侄' + des, []
    # 纯父系
    cls = _cousin_class(k, j, True)
    return _junior_role_name(r, cg, cls)


def name_uncle(pp, ey, eyg):
    """P^k E/Y 长辈旁系本身。pp: 祖先链(生成元列表), ey: 'E'/'Y', eyg: 该旁系性别。"""
    k = len(pp)
    if k == 1:
        prim = UNCLE1[(pp[0].gender, ey, eyg)]
        generic = {(MALE, FEMALE): ['姑妈', '姑母', '姑姑'],
                   (FEMALE, MALE): ['舅舅', '舅父'],
                   (FEMALE, FEMALE): ['姨妈', '姨母']}.get((pp[0].gender, eyg), [])
        return prim, generic
    if k == 2:
        prim = UNCLE2[(pp[0].gender, pp[1].gender, ey, eyg)]
        alts = []
        if (pp[0].gender, pp[1].gender, eyg) == (MALE, FEMALE, MALE):
            alts = ['舅爷爷']           # f,m,xb 的通用词形
        return prim, alts
    # k>=3：线前缀（伯/叔/姑/舅/姨，由最近一位祖先性别决定）+ 祖称（末字按该旁系性别）
    anc = _formal_ancestor([g.gender for g in pp])
    anc = anc[:-1] + ('父' if eyg == MALE else '母')
    line = _mate_uncle_line(list(pp), ey, eyg)
    prim = line + anc
    alts = [('伯叔' if eyg == MALE else '姑') + anc]
    return prim, alts


def _junior_role_name(role, gender, class_prefix):
    """堂/从/族系在 role 处的呼称。role: 相对"我"的代数差（0=同辈…负数=长辈）。"""
    if role == 0:
        if gender == MALE:
            return class_prefix + '兄弟', [class_prefix + '哥', class_prefix + '弟']
        return class_prefix + '姐妹', [class_prefix + '姐', class_prefix + '妹']
    if role == -1:
        if gender == MALE:
            return class_prefix + '伯叔父', [class_prefix + '伯', class_prefix + '叔',
                                             class_prefix + '伯父', class_prefix + '叔父']
        return class_prefix + '姑', []
    if role <= -2:
        anc = _formal_ancestor([MALE] * (-role))
        if gender == MALE:
            return class_prefix + '伯叔' + anc, [class_prefix + '伯' + anc,
                                                 class_prefix + '叔' + anc]
        if role == -2:
            return '姑祖母', [class_prefix + '姑祖母']
        return '曾' * (-role - 2) + '姑祖母', [class_prefix + '姑']
    # role >= 1
    if role == 1:
        return class_prefix + ('侄' if gender == MALE else '侄女'), []
    if role == 2:
        return class_prefix + ('侄孙' if gender == MALE else '侄孙女'), []
    des, _ = name_descendants([MALE] * (role - 1) + [gender])
    return class_prefix + '侄' + des, []


def _cousin_class(k, j, pure_pat):
    """纯父系堂表支的"类"前缀：堂/从/从堂/族/四从父。"""
    if j == 1:
        return '堂'
    if k == 2:
        return '从堂'
    if k == 3:
        return '从' if j == 2 else '族'
    if j == 2:
        return '从堂'
    if j == 3:
        return '族'
    if j == 4:
        return '四从父'
    return '族'


def name_cousin_mate(pp, ey, eyg, rest, mg):
    """P^k E/Y C^j M：堂表亲的配偶。"""
    k = len(pp)
    j = len(rest)
    cg = rest[-1].gender
    r = j - k
    # k==1 且 r==0：堂/表兄弟姐妹的配偶
    if k == 1 and r == 0:
        if pp[0].gender == MALE and eyg == MALE:
            cls = '堂'
        elif pp[0].gender == MALE:
            cls = '姑表'
        elif eyg == MALE:
            cls = '舅表'
        else:
            cls = '姨'
        if cg == MALE:
            return (cls + '嫂', [cls + '弟媳']) if mg == FEMALE else (cls + '兄婿', [cls + '弟婿'])
        return (cls + '姐夫', [cls + '妹夫']) if mg == MALE else (cls + '姐嫂', [cls + '妹媳'])
    # k==2 且 j==1：父/母之堂表兄弟姐妹的配偶
    if k == 2 and j == 1:
        key = (pp[0].gender, pp[1].gender, eyg)
        if cg == MALE:
            a, b = COUSIN2_MALE[key]
            if mg == FEMALE:
                if key == (MALE, MALE, MALE):
                    return '堂伯母', ['堂婶']
                if a == '堂舅':
                    return '堂舅妈', []
                return (a[:-1] + '母', [b[:-1] + '母'])
            return (a + '婿', [b + '婿'])
        a, b = COUSIN2_FEMALE[key]
        if mg == MALE:
            if a == '堂姑':
                return '堂姑丈', []
            if a == '堂姨':
                return '堂姨丈', []
            return (a[:-1] + '父', [])
        return (a.rstrip('母') + '媳', [])
    # 其余：按"堂表亲名 + 末字按配偶性别"（库词形，如 堂伯祖父→堂伯祖母）
    prim, alts = name_cousin_line(pp, ey, eyg, rest)
    if r == 0:
        if cg == MALE:
            return (prim[:-2] + '嫂', [prim[:-2] + '弟媳']) if mg == FEMALE \
                else (prim[:-2] + '兄婿', [prim[:-2] + '弟婿'])
        return (prim[:-2] + '姐夫', [prim[:-2] + '妹夫']) if mg == MALE \
            else (prim[:-2] + '姐嫂', [prim[:-2] + '妹媳'])
    if prim.endswith('父'):
        return prim[:-1] + ('父' if mg == MALE else '母'), \
            [a[:-1] + ('父' if mg == MALE else '母') for a in alts]
    if prim.endswith('母'):
        return prim[:-1] + ('父' if mg == MALE else '母'), []
    if prim.endswith('女'):
        keep = prim + ('婿' if mg == MALE else '媳')
        alts = [prim[:-1] + ('婿' if mg == MALE else '媳')]
        if '外甥' in prim:
            alts.append(prim.replace('外甥', '甥')[:-1] + ('婿' if mg == MALE else '媳'))
        return keep, alts
    if mg == FEMALE:
        if prim.startswith('堂') or prim.endswith(('孙', '曾孙', '玄孙', '来孙', '晜孙')):
            return prim + '媳妇', [prim + '妇']
        base = prim.replace('外甥', '甥') if '外甥' in prim else prim
        return base + '妇', [prim + '妇', prim + '媳妇']
    return prim + '婿', []


def name_sibling_line(ey, eyg, rest):
    """E/Y C^j：兄弟姐妹的子女及更远支系（rest 为 C 链）。"""
    if not rest:
        return SIB[ey][eyg], SIB_ALTS[ey][eyg]
    j = len(rest)
    cg = rest[-1].gender
    if j == 1:
        if eyg == MALE:
            return '侄' + ('子' if cg == MALE else '女'), []
        return '外甥' + ('' if cg == MALE else '女'), []
    # j>=2：侄/甥 + 对 C^j 链套用直系晚辈的"外"规则（侄外孙/甥外孙…）
    if eyg == MALE:
        core = '侄'
    else:
        core = '甥'
    des = _formal_descendant([g.gender for g in rest])
    return core + des, []


def name_sibling_mate(ey, eyg, mg):
    """E/Y M：兄弟姐妹的配偶（含同性）。"""
    table = {
        ('E', MALE): {FEMALE: ('嫂子', []), MALE: ('兄婿', [])},
        ('Y', MALE): {FEMALE: ('弟媳', ['弟妹']), MALE: ('弟婿', [])},
        ('E', FEMALE): {MALE: ('姐夫', []), FEMALE: ('姐嫂', [])},
        ('Y', FEMALE): {MALE: ('妹夫', []), FEMALE: ('妹媳', [])},
    }
    return table[(ey, eyg)][mg]


def name_nephew_mate(ey, eyg, rest, mg):
    """E/Y C^j M：侄/甥的配偶（含同性）。"""
    j = len(rest)
    cg = rest[-1].gender
    if eyg == MALE:
        core = '侄'
    else:
        core = '甥'
    if j == 1:
        if cg == MALE:
            return (core + '媳妇', [core + '媳']) if mg == FEMALE else (core + '婿', [])
        return (core + '女婿', []) if mg == MALE else (core + '女媳', [])
    # j>=2：侄孙辈的配偶（库词形：+妇/+婿，女字在婿前省略）
    base = core + _formal_descendant([g.gender for g in rest])
    if base.endswith('女'):
        if mg == MALE:
            return base[:-1] + '婿', []
        return base + '媳', []
    if mg == FEMALE:
        return base + '妇', []
    return base + '婿', []


# ----------------------------------------------------------------------------
# 姻亲：以 Mate 开头的链（配偶的亲属）
# ----------------------------------------------------------------------------

MATE_SIB = {   # (配偶性别, E/Y, 旁系性别) -> 呼称
    (FEMALE, 'E', MALE): '大舅子', (FEMALE, 'Y', MALE): '小舅子',
    (FEMALE, 'E', FEMALE): '大姨子', (FEMALE, 'Y', FEMALE): '小姨子',
    (MALE, 'E', MALE): '大伯子', (MALE, 'Y', MALE): '小叔子',
    (MALE, 'E', FEMALE): '大姑子', (MALE, 'Y', FEMALE): '小姑子',
}

MATE_SIB_MATE = {   # 配偶的兄弟姐妹的配偶（异性；同性类推 +婿/+媳）
    (FEMALE, 'E', MALE): {FEMALE: '大舅妇', MALE: '大舅子婿'},
    (FEMALE, 'Y', MALE): {FEMALE: '小舅妇', MALE: '小舅子婿'},
    (FEMALE, 'E', FEMALE): {MALE: '大姨夫', FEMALE: '大姨子媳'},
    (FEMALE, 'Y', FEMALE): {MALE: '小姨夫', FEMALE: '小姨子媳'},
    (MALE, 'E', MALE): {FEMALE: '大婶子', MALE: '大伯子婿'},
    (MALE, 'Y', MALE): {FEMALE: '小婶子', MALE: '小叔子婿'},
    (MALE, 'E', FEMALE): {MALE: '大姑夫', FEMALE: '大姑子媳'},
    (MALE, 'Y', FEMALE): {MALE: '小姑夫', FEMALE: '小姑子媳'},
}

MATE_NEPHEW = {   # 配偶的侄甥（库主词形；备选词形为 内侄/夫侄 等）
    (FEMALE, MALE, MALE): ('舅侄', ['内侄', '妻侄子']), (FEMALE, MALE, FEMALE): ('舅侄女', ['内侄女', '妻侄女']),
    (FEMALE, FEMALE, MALE): ('姨甥', ['妻甥男']), (FEMALE, FEMALE, FEMALE): ('姨甥女', ['妻甥女']),
    (MALE, MALE, MALE): ('叔侄', ['夫侄子']), (MALE, MALE, FEMALE): ('叔侄女', ['夫侄女']),
    (MALE, FEMALE, MALE): ('姑甥', ['夫甥男']), (MALE, FEMALE, FEMALE): ('姑甥女', ['夫甥女']),
}

# 配偶之父母（1 代）
MATE_PARENT = {
    (FEMALE, MALE): '岳父', (FEMALE, FEMALE): '岳母',
    (MALE, MALE): '公公', (MALE, FEMALE): '婆婆',
}

# 配偶之父/母的兄弟姐妹（1 代上）
MATE_UNCLE1 = {
    (FEMALE, MALE, 'E', MALE): '伯岳父', (FEMALE, MALE, 'Y', MALE): '叔岳父',
    (FEMALE, MALE, 'E', FEMALE): '姑岳母', (FEMALE, MALE, 'Y', FEMALE): '姑岳母',
    (FEMALE, FEMALE, 'E', MALE): '舅岳父', (FEMALE, FEMALE, 'Y', MALE): '舅岳父',
    (FEMALE, FEMALE, 'E', FEMALE): '姨岳母', (FEMALE, FEMALE, 'Y', FEMALE): '姨岳母',
    (MALE, MALE, 'E', MALE): '伯公父', (MALE, MALE, 'Y', MALE): '叔公父',
    (MALE, MALE, 'E', FEMALE): '姑婆母', (MALE, MALE, 'Y', FEMALE): '姑婆母',
    (MALE, FEMALE, 'E', MALE): '舅公父', (MALE, FEMALE, 'Y', MALE): '舅公父',
    (MALE, FEMALE, 'E', FEMALE): '姨婆母', (MALE, FEMALE, 'Y', FEMALE): '姨婆母',
}


def _formal_ancestor(gs):
    """直系祖先的正式词形（父/母/祖父/祖母/外祖父/外祖母/曾祖父…）。"""
    if len(gs) == 1:
        return '父' if gs[0] == MALE else '母'
    if len(gs) == 2:
        return {(MALE, MALE): '祖父', (MALE, FEMALE): '祖母',
                (FEMALE, MALE): '外祖父', (FEMALE, FEMALE): '外祖母'}[(gs[0], gs[1])]
    prim, _ = name_ancestors(list(gs))
    return prim


def _mate_uncle_line(pp, ey, eyg):
    """配偶之伯叔姑舅姨的"线"前缀：伯/叔/姑/舅/姨（由最近一位祖先的性别决定）。"""
    last = pp[-1].gender
    if eyg == MALE:
        if last == MALE:
            return '伯' if ey == 'E' else '叔'
        return '舅'
    if last == MALE:
        return '姑'
    return '姨'


def _mate_ancestor_insert(base, mg):
    """把配偶的祖先名按性别插入 岳 / 公、婆。base 形如 祖父/祖母/曾祖父/外曾外祖母…"""
    if base.endswith(('父', '母', '祖')):
        if mg == FEMALE:
            return base[:-1] + '岳' + base[-1]
        if base[-1] == '父':
            return base[:-1] + '公父'
        if base[-1] == '母':
            return base[:-1] + '婆母'
        return base[:-1] + '公' + base[-1]
    return base



def _mate_sib_mate_names(mg, ey, eyg, m2):
    """配偶的兄弟姐妹的配偶：返回 (主呼称, 备选列表)。"""
    big = MATE_SIB_MATE[(mg, 'E', eyg)][m2]
    small = MATE_SIB_MATE[(mg, 'Y', eyg)][m2]
    alts = [small]
    if (mg, eyg, m2) == (FEMALE, MALE, FEMALE):
        alts += ['大舅嫂', '小舅嫂', '舅嫂']
    if (mg, eyg, m2) == (MALE, FEMALE, MALE):
        alts += ['姑夫']
    if (mg, eyg, m2) == (MALE, MALE, FEMALE):
        alts += ['妯娌']
    if (mg, eyg, m2) == (FEMALE, FEMALE, MALE):
        alts += ['连襟']
    return MATE_SIB_MATE[(mg, ey, eyg)][m2], alts

def name_mate_first(mg, rest):
    """M(g) + rest 的命名。rest 为去掉首位 Mate 后的生成元列表。"""
    if not rest:
        return SPOUSE[mg], SPOUSE_ALTS[mg]
    # 配偶的直系祖先
    if all(isinstance(g, Parent) for g in rest):
        rgs = [g.gender for g in rest]
        if len(rgs) == 1:
            prim = MATE_PARENT[(mg, rgs[0])]
            return prim, []
        if len(rgs) == 2:
            formal = {(MALE, MALE): '祖父', (MALE, FEMALE): '祖母',
                      (FEMALE, MALE): '外祖父', (FEMALE, FEMALE): '外祖母'}
            base = formal[(rgs[0], rgs[1])]
            return _mate_ancestor_insert(base, mg), [('妻' if mg == FEMALE else '夫') + base]
        base, _ = name_ancestors(rgs)
        return _mate_ancestor_insert(base, mg), [('妻' if mg == FEMALE else '夫') + base]
    # 配偶的兄弟姐妹（仅一位 E/Y）
    if len(rest) == 1 and isinstance(rest[0], (Elder, Younger)):
        ey = 'E' if isinstance(rest[0], Elder) else 'Y'
        eyg = rest[0].gender
        generic = {(MALE, FEMALE): ['姑子', '夫姑'],
                   (FEMALE, MALE): ['舅子', '妻舅'],
                   (FEMALE, FEMALE): ['姨子', '妻姨']}.get((mg, eyg), [])
        return MATE_SIB[(mg, ey, eyg)], generic
    # 配偶的兄弟姐妹的配偶：M E/Y M（含同性：+婿/+媳）
    if len(rest) == 2 and isinstance(rest[0], (Elder, Younger)) \
            and isinstance(rest[1], Mate):
        ey = 'E' if isinstance(rest[0], Elder) else 'Y'
        eyg = rest[0].gender
        m2 = rest[1].gender
        return _mate_sib_mate_names(mg, ey, eyg, m2)
    # 配偶的侄甥的配偶：M E/Y C^j M
    if len(rest) >= 3 and isinstance(rest[0], (Elder, Younger)) \
            and all(isinstance(g, Child) for g in rest[1:-1]) \
            and isinstance(rest[-1], Mate):
        eyg = rest[0].gender
        cgs = [g.gender for g in rest[1:-1]]
        m2 = rest[-1].gender
        core, _ = MATE_NEPHEW[(mg, eyg, cgs[-1])]
        stem = core[:-1] if core.endswith('女') else core
        if len(cgs) == 1:
            base = core
        else:
            base = stem + _formal_descendant(cgs)
        if base.endswith('女'):
            return (base + '婿' if m2 == MALE else base + '媳'), []
        return (base + ('妇' if m2 == FEMALE else '婿')) if len(cgs) >= 2 \
            else (base + '媳妇' if m2 == FEMALE else base + '婿'), []
    # 配偶的兄弟姐妹的配偶的亲属：M E/Y M …（叔兄弟眷父/叔兄弟眷舅父…）
    if len(rest) >= 3 and isinstance(rest[0], (Elder, Younger)) \
            and isinstance(rest[1], Mate):
        seg = _inlaw_segment_prefix([Mate(mg), rest[0]], rest[1].gender)
        if seg:
            rname = _inlaw_rest_name(rest[1].gender, 0, rest[2:])
            if rname:
                if isinstance(rname, tuple):
                    return seg + rname[0], [seg + a for a in rname[1]]
                return seg + rname, []
    # 配偶的侄甥之姻亲：M E/Y C^j M …（叔侄姻兄弟/舅侄眷男…）
    if len(rest) >= 3 and isinstance(rest[0], (Elder, Younger)) \
            and isinstance(rest[1], Child):
        ti = next((i for i in range(2, len(rest)) if isinstance(rest[i], Mate)), None)
        if ti is not None:
            eyg = rest[0].gender
            cgs = [g.gender for g in rest[1:ti]]
            core, _ = MATE_NEPHEW[(mg, eyg, cgs[-1])]
            stem = core[:-1] if core.endswith('女') else core
            if len(cgs) == 1:
                prefix, s2 = stem, -1
            else:
                prefix, s2 = stem + _formal_descendant(cgs), -len(cgs)
            m2 = rest[ti].gender
            rname = _inlaw_rest_name(m2, s2, rest[ti + 1:])
            if rname:
                base = prefix + ('眷' if m2 == FEMALE else '姻')
                if isinstance(rname, tuple):
                    return base + rname[0], [base + a for a in rname[1]]
                return base + rname, []
    # 配偶的侄甥
    if isinstance(rest[0], (Elder, Younger)) and len(rest) > 1 and \
            all(isinstance(g, Child) for g in rest[1:]):
        eyg = rest[0].gender
        j = len(rest) - 1
        core, alts = MATE_NEPHEW[(mg, eyg, rest[-1].gender)]
        if j == 1:
            return core, alts
        stem = core[:-1] if core.endswith('女') else core
        return stem + _formal_descendant([g.gender for g in rest[1:]]), alts
    # 配偶的伯叔姑舅姨：M P^k E/Y …（其后接 C^j 或 M 的情况分别处理）
    if isinstance(rest[0], Parent):
        k = 1
        while k < len(rest) and isinstance(rest[k], Parent):
            k += 1
        if k < len(rest) and isinstance(rest[k], (Elder, Younger)):
            ey = 'E' if isinstance(rest[k], Elder) else 'Y'
            eyg = rest[k].gender
            tail = rest[k + 1:]
            if not tail:
                if k == 1:
                    prim = MATE_UNCLE1[(mg, rest[0].gender, ey, eyg)]
                    return prim, []
                # k>=2：线前缀（伯/叔/姑/舅/姨）+ 配偶祖辈基（岳/公婆 按性别插入）
                line = _mate_uncle_line(list(rest[:k]), ey, eyg)
                base = _mate_ancestor_insert(
                    _formal_ancestor([g.gender for g in rest[:k]]), mg)
                if base.endswith(('公父', '婆母')):
                    base = base[:-2] + ('公父' if eyg == MALE else '婆母')
                else:
                    base = base[:-1] + ('父' if eyg == MALE else '母')
                prim = line + base
                uprim, ualts = name_uncle(list(rest[:k]), ey, eyg)
                other = '妻' if mg == FEMALE else '夫'
                alts = [('岳' if mg == FEMALE else '公') + uprim,
                        other + uprim] + [other + a for a in ualts]
                return prim, alts
            if all(isinstance(g, Child) for g in tail):
                if k == 1 and len(tail) == 1:
                    # 配偶的堂表兄弟姐妹：堂大伯子/堂小叔子/堂大姑子/堂大舅子…
                    line = {(MALE, MALE): '堂', (MALE, FEMALE): '姑表',
                            (FEMALE, MALE): '舅表',
                            (FEMALE, FEMALE): '姨'}[(rest[0].gender, eyg)]
                    if tail[-1].gender == MALE:
                        stem = '舅子' if mg == FEMALE else '伯子'
                        alt_stem = '舅子' if mg == FEMALE else '叔子'
                    else:
                        stem = '姨子' if mg == FEMALE else '姑子'
                        alt_stem = stem
                    return line + '大' + stem, [line + '小' + alt_stem]
                if k == 2 and len(tail) == 1:
                    # 妻方纯父系堂舅：库词形 姻伯丈/姻叔丈（女：姻姆）
                    if mg == FEMALE and rest[0].gender == MALE \
                            and rest[1].gender == MALE and eyg == MALE:
                        if tail[-1].gender == MALE:
                            return '姻伯丈', ['姻叔丈']
                        return '堂姑岳母', []
                    # 配偶祖辈的堂表兄弟姐妹：堂伯公父/堂姑婆母/…（线1×线2+岳/公终端）
                    line1 = {(MALE, MALE): '堂', (MALE, FEMALE): '姑表',
                             (FEMALE, MALE): '舅表',
                             (FEMALE, FEMALE): '姨'}[(rest[1].gender, eyg)]
                    if rest[0].gender == MALE:
                        if tail[-1].gender == MALE:
                            suf = '岳父' if mg == FEMALE else '公父'
                            return line1 + '伯' + suf, [line1 + '叔' + suf]
                        suf = '岳母' if mg == FEMALE else '婆母'
                        return line1 + '姑' + suf, []
                    if tail[-1].gender == MALE:
                        suf = '岳父' if mg == FEMALE else '公父'
                        return line1 + '舅' + suf, []
                    suf = '岳母' if mg == FEMALE else '婆母'
                    return line1 + '姨' + suf, []
                # 其余（k>=1 且 j>=2，或 k>=3 且 j==1）：配偶视角完整命名
                base, alts4 = name_cousin_line(list(rest[:k]), ey, eyg, tail)
                if k > len(tail):        # r = j-k < 0：岳/公父/婆母 终端插入
                    ins = _mate_ancestor_insert(base, mg)
                    ins_alts = []
                    for a in alts4:
                        ia = _mate_ancestor_insert(a, mg)
                        if ia != a and ia not in ins_alts:
                            ins_alts.append(ia)
                    return ins, ins_alts
                pref = '夫' if mg == MALE else '妻'
                return pref + base, [pref + a for a in alts4]
            # 配偶堂表兄弟姐妹的配偶：堂大婶子/堂大姑夫/堂大舅嫂…
            if k == 1 and len(tail) == 2 and isinstance(tail[0], Child) \
                    and isinstance(tail[1], Mate):
                line = {(MALE, MALE): '堂', (MALE, FEMALE): '姑表',
                        (FEMALE, MALE): '舅表',
                        (FEMALE, FEMALE): '姨'}[(rest[0].gender, eyg)]
                big, alts5 = _mate_sib_mate_names(mg, 'E', tail[0].gender,
                                                    tail[1].gender)
                return line + big, [line + a for a in alts5 if a != big]
            # 配偶之高辈旁系的配偶：M P^k E/Y M（k>=2）
            if k >= 2 and len(tail) == 1 and isinstance(tail[0], Mate):
                line = _mate_uncle_line(list(rest[:k]), ey, eyg)
                m2 = tail[0].gender
                base = _mate_ancestor_insert(
                    _formal_ancestor([g.gender for g in rest[:k]]), mg)
                if base.endswith(('公父', '婆母')):
                    base = base[:-2] + ('公父' if m2 == MALE else '婆母')
                else:
                    base = base[:-1] + ('父' if m2 == MALE else '母')
                if m2 == eyg:
                    return line + base + ('婿' if m2 == MALE else '媳'), []
                return line + base, []
            # tail 中再含配偶：段前缀 + 重锚命名（如 夫叔眷外祖父）
            if any(isinstance(g, Mate) for g in tail):
                ti = next(idx for idx, g in enumerate(tail) if isinstance(g, Mate))
                seg = _inlaw_segment_prefix(list(rest[:k]) + [rest[k]] + tail[:ti],
                                            tail[ti].gender)
                if seg:
                    s = priority(KinMonomial(list(rest[:k]) + [rest[k]] + tail[:ti]))
                    rname = _inlaw_rest_name(tail[ti].gender, s, tail[ti + 1:])
                    if rname:
                        if isinstance(rname, tuple):
                            return ('夫' if mg == MALE else '妻') + seg + rname[0], \
                                [('夫' if mg == MALE else '妻') + seg + a for a in rname[1]]
                        return ('夫' if mg == MALE else '妻') + seg + rname, []
                # 重锚失败且 tail 不是“纯 C 链 + 末位 M”时，name_cousin_mate
                # 无法处理（如 tail 以 M 开头）；直接按绝对辈分兜底。
                if not (all(isinstance(g, Child) for g in tail[:-1])
                        and isinstance(tail[-1], Mate)):
                    tg = priority(KinMonomial(rest))
                    return ('妻' if mg == FEMALE else '夫') + \
                        _term_at_generation(tg, rest[-1].gender), []
            # 后面还有配偶：配偶之表亲的配偶（r<0 做终端插入，否则 夫/妻 + 配偶视角）
            base, _ = name_cousin_mate(list(rest[:k]), ey, eyg, tail[:-1], tail[-1].gender)
            if k > len(tail) - 1:
                return _mate_ancestor_insert(base, mg), []
            return ('夫' if mg == MALE else '妻') + base, []
    # 兜底：配偶之深支。用“妻/夫 + 目标绝对辈分词”，避免把 rest 的
    # 相对辈分误当成绝对辈分（如 妻舅表外曾曾孙婿 这类错位）。
    tg = priority(KinMonomial(rest))
    tsex = rest[-1].gender
    return ('妻' if mg == FEMALE else '夫') + _term_at_generation(tg, tsex), []


# ----------------------------------------------------------------------------
# 以 Mate 结尾的链：某人的配偶
# ----------------------------------------------------------------------------

def name_mate_last(mg, X):
    """X M(g)：X 的配偶。X 为去掉末位 Mate 的生成元列表。"""
    n = len(X)
    if n == 0:
        return SPOUSE[mg], SPOUSE_ALTS[mg]
    # 兄弟姐妹的配偶
    if n == 1 and isinstance(X[0], (Elder, Younger)):
        ey = 'E' if isinstance(X[0], Elder) else 'Y'
        return name_sibling_mate(ey, X[0].gender, mg)
    # 子女/孙辈的配偶
    if all(isinstance(g, Child) for g in X):
        if n == 1:
            if X[0].gender == MALE:
                return ('儿媳', []) if mg == FEMALE else ('儿婿', [])
            return ('女婿', []) if mg == MALE else ('女媳', [])
        base = _formal_descendant([g.gender for g in X])
        if n == 2:
            if base.endswith('女'):
                return (base + '婿', []) if mg == MALE else (base + '媳', [])
            return (base + '媳妇', []) if mg == FEMALE else (base + '婿', [])
        # n>=3：库词形 媳妇/妇 并存（曾孙妇/曾孙媳妇），女婿保留"女"
        if base.endswith('女'):
            return (base + '婿', []) if mg == MALE else (base + '媳', [])
        return (base + '媳妇', [base + '妇']) if mg == FEMALE else (base + '婿', [])
    # 配偶的侄甥之配偶：X = [M] + E/Y C^j
    if n >= 2 and isinstance(X[0], Mate):
        inner = X[1:]
        if len(inner) >= 2 and isinstance(inner[0], (Elder, Younger)) \
                and all(isinstance(g, Child) for g in inner[1:]):
            eyg = inner[0].gender
            cgs = [g.gender for g in inner[1:]]
            core, _ = MATE_NEPHEW[(X[0].gender, eyg, cgs[-1])]
            stem = core[:-1] if core.endswith('女') else core
            if len(cgs) == 1:
                base = core
                if base.endswith('女'):
                    return (base + '婿' if mg == MALE else base + '媳'), []
                return (base + '媳妇' if mg == FEMALE else base + '婿'), []
            base = stem + _formal_descendant(cgs)
            if base.endswith('女'):
                return (base[:-1] + '婿' if mg == MALE else base + '媳'), []
            return (base + ('妇' if mg == FEMALE else '婿')), []
        k = 1
        while k < len(inner) and isinstance(inner[k], Parent):
            k += 1
        if k >= 1 and k < len(inner) and isinstance(inner[k], (Elder, Younger)) \
                and all(isinstance(g, Parent) for g in inner[:k]):
            ey = 'E' if isinstance(inner[k], Elder) else 'Y'
            eyg = inner[k].gender
            tail = inner[k + 1:]
            if not tail:
                line = _mate_uncle_line(list(inner[:k]), ey, eyg)
                if k == 1:
                    base = {(FEMALE, MALE): '岳父', (FEMALE, FEMALE): '岳母',
                            (MALE, MALE): '公父', (MALE, FEMALE): '婆母'}[(X[0].gender, mg)]
                    if mg == eyg:              # 同性配偶：+婿/+媳
                        return line + base + ('婿' if mg == MALE else '媳'), []
                else:
                    base = _mate_ancestor_insert(
                        _formal_ancestor([g.gender for g in inner[:k]]), X[0].gender)
                    if base.endswith(('公父', '婆母')):
                        base = base[:-2] + ('公父' if mg == MALE else '婆母')
                    else:
                        base = base[:-1] + ('父' if mg == MALE else '母')
                    if mg == eyg:              # 同性配偶：+婿/+媳
                        return line + base + ('婿' if mg == MALE else '媳'), []
                return line + base, []
            if len(tail) == 1 and isinstance(tail[0], Child):
                if k == 1:
                    # 配偶堂表兄弟姐妹的配偶（库词形）：堂大姑夫/堂大婶子/堂大舅嫂…
                    line = {(MALE, MALE): '堂', (MALE, FEMALE): '姑表',
                            (FEMALE, MALE): '舅表',
                            (FEMALE, FEMALE): '姨'}[(inner[0].gender, eyg)]
                    big, alts6 = _mate_sib_mate_names(X[0].gender, 'E',
                                                        tail[0].gender, mg)
                    return line + big, [line + a for a in alts6 if a != big]
                # k>=2：配偶之高辈表亲的配偶（夫/妻 + 配偶视角；r<0 做终端插入）
                base, alts7 = name_cousin_mate(list(inner[:k]), ey, eyg, tail, mg)
                if k > len(tail):
                    ins = _mate_ancestor_insert(base, X[0].gender)
                    return ins, []
                pref = '夫' if X[0].gender == MALE else '妻'
                return pref + base, [pref + a for a in alts7]
    # 伯叔姑舅姨/堂表亲的配偶
    if isinstance(X[0], Parent):
        k = 1
        while k < n and isinstance(X[k], Parent):
            k += 1
        if k < n and isinstance(X[k], (Elder, Younger)):
            ey = 'E' if isinstance(X[k], Elder) else 'Y'
            eyg = X[k].gender
            tail = X[k + 1:]
            if not tail:
                pp = list(X[:k])
                if k == 1:
                    prim, ualts = UNCLE1_MATE[(pp[0].gender, ey, eyg)][mg]
                    return prim, ualts
                if k == 2:
                    if mg in UNCLE2_MATE.get((pp[0].gender, pp[1].gender, ey, eyg), {}):
                        prim = UNCLE2_MATE[(pp[0].gender, pp[1].gender, ey, eyg)][mg]
                        alts = ['舅奶奶'] if (pp[0].gender, pp[1].gender, eyg) == \
                            (MALE, FEMALE, MALE) else []
                        return prim, alts
                    # 同性配偶（如 伯公之夫/姑奶奶之妻）：+婿/+媳
                    base, _ = name_uncle(pp, ey, eyg)
                    return base + ('婿' if mg == MALE else '媳'), []
                # k>=3：线前缀 + 祖称（末字按配偶性别；同性配偶 +婿/+媳）
                anc = _formal_ancestor([g.gender for g in pp])
                anc = anc[:-1] + ('父' if mg == MALE else '母')
                line = _mate_uncle_line(list(pp), ey, eyg)
                _, ualts = name_uncle(list(pp), ey, eyg)
                if mg == eyg:
                    return line + anc + ('婿' if mg == MALE else '媳'), []
                return line + anc, [a[:-1] + ('父' if mg == MALE else '母')
                                    for a in ualts]
            if all(isinstance(g, Child) for g in tail):
                return name_cousin_mate(list(X[:k]), ey, eyg, tail, mg)
    # 配偶的兄弟姐妹的配偶（含同性：+婿/+媳）
    if n == 2 and isinstance(X[0], Mate) and isinstance(X[1], (Elder, Younger)):
        ey = 'E' if isinstance(X[1], Elder) else 'Y'
        return _mate_sib_mate_names(X[0].gender, ey, X[1].gender, mg)
    # 侄/甥的配偶
    if n >= 1 and isinstance(X[0], (Elder, Younger)) and \
            all(isinstance(g, Child) for g in X[1:]):
        ey = 'E' if isinstance(X[0], Elder) else 'Y'
        return name_nephew_mate(ey, X[0].gender, X[1:], mg)
    # 姻侄媳/姻侄婿：X = [C, M, E/Y]（主表词形）
    if n == 3 and isinstance(X[0], Child) and isinstance(X[1], Mate) \
            and isinstance(X[2], (Elder, Younger)):
        return ('姻侄媳' if mg == FEMALE else '姻侄婿'), []
    # 段前缀 + 重锚：X 内含 Mate（不限 X 的首段类型）
    # 例：父之母之姐之妻之兄 + 妻 → 段前缀“姨祖眷” + 重锚“舅祖母”
    if n >= 2 and any(isinstance(g, Mate) for g in X):
        ti = next(i for i, g in enumerate(X) if isinstance(g, Mate))
        if 0 < ti < n - 1:
            seg = _inlaw_segment_prefix(X[:ti], X[ti].gender)
            if seg:
                s = priority(KinMonomial(X[:ti]))
                rname = _inlaw_rest_name(X[ti].gender, s, X[ti + 1:] + [Mate(mg)])
                if rname:
                    if isinstance(rname, tuple):
                        return seg + rname[0], [seg + a for a in rname[1]]
                    return seg + rname, []
    # 泛化：按 X 末位性别套用 媳/婿/妇 后缀（用于 舅侄媳妇/侄姻妇 等复合姻亲链）
    prim, alts = name_km(X)
    if prim.endswith(('兄', '弟', '姐', '妹', '姊')):
        return (prim + ('妇' if mg == FEMALE else '婿'),
                [a + ('妇' if mg == FEMALE else '婿') for a in alts if a != prim])
    # 口语兄弟姐妹词 + 配偶：用“嫂子/弟媳/姐夫/妹夫”等替换，
    # 而不是“哥哥媳妇/姐姐婿”这种机械拼接（仅段前缀分支不适用时的兜底）。
    _COLLOQUIAL_SIB = {'哥哥': ('E', MALE), '姐姐': ('E', FEMALE),
                       '弟弟': ('Y', MALE), '妹妹': ('Y', FEMALE)}
    for _sib, (_ey, _eyg) in _COLLOQUIAL_SIB.items():
        if prim.endswith(_sib):
            _sm, _salts = name_sibling_mate(_ey, _eyg, mg)
            _stem = prim[:-len(_sib)]
            _out = [_stem + a for a in _salts]
            for a in alts:
                if a == prim:
                    continue
                _out.append(_stem + _sm if a.endswith(_sib)
                            else a + ('妇' if mg == FEMALE else '婿'))
            return _stem + _sm, list(dict.fromkeys(_out))
    if prim.endswith('父'):
        return prim[:-1] + ('父' if mg == MALE else '母'), \
            [a[:-1] + ('父' if mg == MALE else '母') for a in alts if a != prim]
    if prim.endswith('母'):
        return prim[:-1] + ('父' if mg == MALE else '母'), \
            [a[:-1] + ('父' if mg == MALE else '母') for a in alts if a != prim]
    if prim.startswith(('叔侄', '舅侄', '姑甥', '姨甥')) \
            and prim.endswith(('侄女', '甥女')):
        return (prim + ('婿' if mg == MALE else '媳')), []
    if prim.endswith('男'):
        base = prim[:-1]
        # 只有“孙/侄/甥…”这类本身带辈分的词才能省掉“男”；
        # “叔男/姑男”省掉后只剩“叔/姑”，会被读成 +1 辈。
        if base.endswith(('孙', '侄', '甥', '子', '女')):
            prim = base
        return (prim + ('妇' if mg == FEMALE else '婿')), []
    if prim.endswith('女'):
        base = prim[:-1]
        if base.endswith(('孙', '侄', '甥', '子', '女')):
            prim = base
        return (prim + ('婿' if mg == MALE else '媳')), []
    if X[-1].gender == MALE:
        return (prim + '媳妇' if mg == FEMALE else prim + '婿'), []
    return (prim + '婿' if mg == MALE else prim + '媳'), []


# ----------------------------------------------------------------------------
# 配偶在中间：X M(g) Y
# ----------------------------------------------------------------------------

# ----------------------------------------------------------------------------
# 姻亲（眷/姻）体系：X M(g) Y 中段的"段前缀"与重锚命名
# ----------------------------------------------------------------------------

def _inlaw_segment_prefix(X, mg):
    """[X, M(g)] 段 → 库中的 眷/姻 段前缀（如 男眷/女姻/侄眷/叔眷/舅兄弟眷…）。"""
    n = len(X)
    if n == 1:
        x = X[0]
        if isinstance(x, Child):
            # 男/女 取 X 的性别，眷/姻 取配偶性别（同性婚姻同样适用）
            return ('男' if x.gender == MALE else '女') + \
                ('眷' if mg == FEMALE else '姻')
        if isinstance(x, (Elder, Younger)):
            return ('兄弟' if x.gender == MALE else '姊妹') + \
                ('眷' if mg == FEMALE else '姻')
        return None
    if n == 2:
        a, b = X
        if isinstance(a, Child) and isinstance(b, Child):
            return ('孙' if a.gender == MALE else '外孙') + \
                ('眷' if mg == FEMALE else '姻')
        if isinstance(a, (Elder, Younger)) and isinstance(b, Child):
            return ('侄' if a.gender == MALE else '甥') + \
                ('眷' if mg == FEMALE else '姻')
        if isinstance(a, Parent) and isinstance(b, (Elder, Younger)):
            base = {(MALE, MALE): '叔', (FEMALE, MALE): '舅',
                    (MALE, FEMALE): '姑', (FEMALE, FEMALE): '姨'}[(a.gender, b.gender)]
            return base + ('眷' if mg == FEMALE else '姻')
        if isinstance(a, Mate) and isinstance(b, (Elder, Younger)):
            base = {(MALE, MALE): '叔兄弟', (FEMALE, MALE): '舅兄弟',
                    (MALE, FEMALE): '姑姊妹', (FEMALE, FEMALE): '姨姊妹'}[(a.gender, b.gender)]
            return base + ('眷' if mg == FEMALE else '姻')
        return None
    if n == 3 and isinstance(X[0], Parent) and isinstance(X[1], Parent) \
            and isinstance(X[2], (Elder, Younger)):
        g1, g2, eyg = X[0].gender, X[1].gender, X[2].gender
        base = {(MALE, MALE, MALE): '叔祖', (MALE, MALE, FEMALE): '姑祖',
                (MALE, FEMALE, MALE): '舅祖', (MALE, FEMALE, FEMALE): '姨祖',
                (FEMALE, MALE, MALE): '叔外祖', (FEMALE, MALE, FEMALE): '姑外祖',
                (FEMALE, FEMALE, MALE): '舅外祖', (FEMALE, FEMALE, FEMALE): '姨外祖'}[(g1, g2, eyg)]
        return base + ('眷' if mg == FEMALE else '姻')
    if n >= 3 and isinstance(X[0], Parent) and isinstance(X[1], (Elder, Younger)) \
            and all(isinstance(x, Child) for x in X[2:]):
        g1, eyg = X[0].gender, X[1].gender
        j = n - 2
        if j == 1:
            table = {(MALE, MALE): '从父兄弟眷' if mg == FEMALE else '从父姊妹姻',
                     (MALE, FEMALE): '姑表兄弟眷' if mg == FEMALE else '姑表姊妹姻',
                     (FEMALE, MALE): '舅表兄弟眷' if mg == FEMALE else '舅表姊妹姻',
                     (FEMALE, FEMALE): '从母兄弟眷' if mg == FEMALE else '从母姊妹姻'}
            return table.get((g1, eyg))
        cls = {(MALE, MALE): '堂', (MALE, FEMALE): '姑表',
               (FEMALE, MALE): '舅表', (FEMALE, FEMALE): '姨'}[(g1, eyg)]
        cg = X[-1].gender
        if j == 2:
            stem = '甥' if X[2].gender == FEMALE else '侄'
            return cls + stem + ('眷' if mg == FEMALE else '姻')
        desc = _formal_descendant([MALE] * (j - 2) + [cg])
        return cls + '侄' + desc + ('眷' if mg == FEMALE else '姻')
    if n >= 4 and isinstance(X[0], Parent) and isinstance(X[1], Parent) \
            and isinstance(X[2], (Elder, Younger)) \
            and all(isinstance(x, Child) for x in X[3:]):
        g1, g2, eyg = X[0].gender, X[1].gender, X[2].gender
        j = n - 3
        if j == 1:
            table = {(MALE, MALE, MALE): '从父叔眷' if mg == FEMALE else '从父姑姻',
                     (MALE, MALE, FEMALE): '姑表叔眷' if mg == FEMALE else '姑表姑姻',
                     (MALE, FEMALE, MALE): '舅表叔眷' if mg == FEMALE else '舅表姑姻',
                     (MALE, FEMALE, FEMALE): '从母叔眷' if mg == FEMALE else '从母姑姻',
                     (FEMALE, MALE, MALE): '从父舅眷' if mg == FEMALE else '从父姨姻',
                     (FEMALE, MALE, FEMALE): '姑表舅眷' if mg == FEMALE else '姑表姨姻',
                     (FEMALE, FEMALE, MALE): '舅表舅眷' if mg == FEMALE else '舅表姨姻',
                     (FEMALE, FEMALE, FEMALE): '从母舅眷' if mg == FEMALE else '从母姨姻'}
            return table.get((g1, g2, eyg))
        cls = K2_L0_CLASS[(g1, g2, eyg, X[3].gender)]
        cg = X[-1].gender
        suf = '眷' if mg == FEMALE else '姻'
        r = j - 2
        if r == 0:
            return cls + ('兄弟' if cg == MALE else '姐妹') + suf
        if r == 1:
            return cls + ('侄' if cg == MALE else '侄女') + suf
        desc = _formal_descendant([MALE] * (r - 1) + [cg])
        return cls + '侄' + desc + suf
    # 高辈旁系段（k>=3）：叔/舅/姑/姨标记 + 外(首链为母) + 祖辈级 + 眷/姻
    if n >= 4 and all(isinstance(x, Parent) for x in X[:-1]) \
            and isinstance(X[-1], (Elder, Younger)):
        k = n - 1
        eyg = X[-1].gender
        mark = {(MALE, MALE): '叔', (MALE, FEMALE): '姑',
                (FEMALE, MALE): '舅', (FEMALE, FEMALE): '姨'}[(X[-2].gender, eyg)]
        outer = '外' if X[0].gender == FEMALE else ''
        lv = _formal_ancestor([MALE] * k)[:-1]           # 祖/曾祖/高祖…
        return mark + outer + lv + ('眷' if mg == FEMALE else '姻')
    # 高辈堂表段（k>=3 且 j>=1）：库的眷/姻构词法
    # j==1：线1翻转（堂→从父、姨→从母）+ 叔/舅/姑/姨标记 + 祖辈级 + 眷/姻
    # j>=2：纯父系取 从/族 类；含外或女性旁系取 线1(翻转)+线2'链；
    #       角色按 r=j-k（-1：标记；0：兄弟/姐妹；1：侄/侄女；更晚辈：侄孙…）
    if n >= 5 and all(isinstance(x, Parent) for x in X[:3]) \
            and isinstance(X[3], (Elder, Younger)) \
            and all(isinstance(x, Child) for x in X[4:]):
        pp = list(X[:3])
        eyg = X[3].gender
        j = n - 4
        cg = X[-1].gender
        suf = '眷' if mg == FEMALE else '姻'
        r = j - 3
        mark = {(MALE, MALE): '叔', (MALE, FEMALE): '姑',
                (FEMALE, MALE): '舅', (FEMALE, FEMALE): '姨'}[(pp[0].gender, cg)]
        if j == 1:
            line = {(MALE, MALE): '从父' if mg == FEMALE else '姑表',
                    (MALE, FEMALE): '舅表' if mg == FEMALE else '从母',
                    (FEMALE, MALE): '从父' if mg == FEMALE else '姑表',
                    (FEMALE, FEMALE): '舅表' if mg == FEMALE else '从母'}[(pp[-1].gender, eyg)]
            lv = _formal_ancestor([MALE] * (-r))[:-1]
            return line + mark + lv + suf
        if all(x.gender == MALE for x in pp) and eyg == MALE:
            cls = _cousin_class(3, j, True)
        else:
            LINE1 = {(MALE, MALE): '从父' if mg == FEMALE else '姑表',
                     (MALE, FEMALE): '舅表' if mg == FEMALE else '从母',
                     (FEMALE, MALE): '从父' if mg == FEMALE else '姑表',
                     (FEMALE, FEMALE): '舅表' if mg == FEMALE else '从母'}[(pp[-1].gender, eyg)]
            LINE2 = {(MALE, MALE): '叔表', (MALE, FEMALE): '姑表',
                     (FEMALE, MALE): '舅表', (FEMALE, FEMALE): '姨表'}
            cls = LINE1 + LINE2[(pp[-2].gender, X[4].gender)]
            for d in range(2, j):
                cls += LINE2[(X[3 + d - 1].gender, X[3 + d].gender)]
        if r <= -2:
            lv = _formal_ancestor([MALE] * (-r))[:-1]
            return cls + lv + suf
        if r == -1:
            return cls + mark + suf
        if r == 0:
            return cls + ('兄弟' if cg == MALE else '姐妹') + suf
        if r == 1:
            return cls + ('侄' if cg == MALE else '侄女') + suf
        desc = _formal_descendant([MALE] * (r - 1) + [cg])
        return cls + '侄' + desc + suf
    # 曾孙辈段：[C^k] k>=3 -> 曾孙眷 / 曾孙姻
    if n >= 3 and all(isinstance(x, Child) for x in X):
        desc = _formal_descendant([x.gender for x in X])
        return desc + ('眷' if mg == FEMALE else '姻')
    # 更深段的侄/甥孙辈眷姻（扩展）：[E/Y, C^j] j>=2
    if n >= 3 and isinstance(X[0], (Elder, Younger)) \
            and all(isinstance(x, Child) for x in X[1:]):
        eyg = X[0].gender
        cgs = [x.gender for x in X[1:]]
        desc = _formal_descendant(cgs)
        core = '侄' if eyg == MALE else '甥'
        if desc.endswith('女'):
            desc = desc[:-1]          # 库词形：侄外孙姻（省略"女"）
        return core + desc + ('眷' if mg == FEMALE else '姻')
    return None


def _rest_primary(rname):
    return rname[0] if isinstance(rname, tuple) else rname


def _inlaw_rest_name(mate_g, s, rest):
    """重锚命名：配偶的亲属余链 rest，配偶在 s 代（相对我）。"""
    if not rest:
        return ''
    # 尾部带配偶：+妇/+婿（如 叔兄妇/孙妇）
    if len(rest) >= 2 and isinstance(rest[-1], Mate):
        raw = _inlaw_rest_name(mate_g, s, rest[:-1])
        if not raw:
            return ''
        suf = '妇' if rest[-1].gender == FEMALE else '婿'

        def _app(b):
            if b.endswith('女') or b.endswith('男'):
                base = b[:-1]
                # 只有基词本身带辈分（孙/侄/甥…）时才去掉男/女；
                # 叔/伯/舅/姑/姨 单独不表辈分，保留男/女以免被读成 +1 辈。
                if base.endswith(('孙', '侄', '甥', '子', '女')):
                    return base + suf
                return b + suf
            if b.endswith(('兄', '弟', '姊', '妹', '兄弟', '姊妹')):
                return b + ('妇' if rest[-1].gender == FEMALE else '婿')
            if b.endswith('父'):
                return b[:-1] + ('父' if rest[-1].gender == MALE else '母')
            if b.endswith('母'):
                return b[:-1] + ('父' if rest[-1].gender == MALE else '母')
            return b + suf

        if isinstance(raw, tuple):
            return _app(raw[0]), [_app(a) for a in raw[1]]
        return _app(raw)
    # ---- 余链中还有配偶（嵌套姻亲）----
    # Y = Y1 + M(g2) + Y2：先把 Y1 段按段前缀命名，再以 M(g2) 为新锚点
    # 递归命名 Y2。s 是"本层配偶"的辈分，Y1 的辈分偏移为 priority(Y1)，
    # 故新锚点辈分 s2 = s + priority(Y1)，目标最终辈分 = s + priority(Y)。
    # 这样末位呼称的辈分始终等于目标的绝对辈分，不会把内层配偶的
    # 祖先链误当成相对第一层配偶的偏移（旧实现会落到 9.5 兜底并把
    # 内层名字整体当成 Y 的名字，导致辈分/性别错位）。
    _mpos = [i for i, g in enumerate(rest) if isinstance(g, Mate)]
    if _mpos:
        ti = _mpos[0]
        X2 = list(rest[:ti])
        mg2 = rest[ti].gender
        Y2 = list(rest[ti + 1:])
        if X2:
            seg2 = _inlaw_segment_prefix(X2, mg2)
            if seg2:
                s2 = s + priority(KinMonomial(X2))
                rname2 = _inlaw_rest_name(mg2, s2, Y2)
                if rname2:
                    if isinstance(rname2, tuple):
                        return seg2 + rname2[0], [seg2 + a for a in rname2[1]]
                    return seg2 + rname2
    # ---- 直系祖先余链 ----
    if all(isinstance(g, Parent) for g in rest):
        gs = [g.gender for g in rest]
        if s >= 1:
            return _formal_ancestor([mate_g] + [MALE] * (s - 1) + gs)
        if s == 0:
            return _formal_ancestor(gs)
        drop = -s
        if len(gs) <= drop:
            gen = s + len(gs)
            if gen == 0:
                return '兄弟' if gs[-1] == MALE else '姊妹'
            if gen == -1:
                return '男' if gs[-1] == MALE else '女'
            return _formal_descendant_at(gen, gs[-1])
        return _formal_ancestor(gs[drop:])
    # ---- 配偶的兄弟姐妹（裸 E/Y）----
    if len(rest) == 1 and isinstance(rest[0], (Elder, Younger)):
        ey = 'E' if isinstance(rest[0], Elder) else 'Y'
        eyg = rest[0].gender
        gen = s
        if gen == 0:
            return SIB_F[ey][eyg], [('兄弟' if eyg == MALE else '姊妹')]
        if gen == 1:
            if mate_g == FEMALE:
                return '舅父' if eyg == MALE else '姨母'
            if eyg == MALE:
                return ('伯父' if ey == 'E' else '叔父'), ['叔伯父']
            return '姑母'
        if gen == 2:
            if mate_g == FEMALE:
                return '舅祖父' if eyg == MALE else '姨祖母'
            return '叔祖父' if eyg == MALE else '姑祖母'
        if gen == -1:
            return '男' if eyg == MALE else '女'
        if gen == -2:
            return '孙男' if eyg == MALE else '孙女'
        if gen <= -3:
            return '曾' * (-gen - 2) + '孙' + ('男' if eyg == MALE else '女')
        if gen >= 3:
            # 目标在原辈分 gen 上：祖名长度应为 gen（旧实现用 gen-1，
            # 且末字固定为"父"，导致高一辈的目标被降一辈并变成男性）。
            base = _formal_ancestor([MALE] * (gen - 1) + [eyg])
            if mate_g == FEMALE:
                return '舅' + base if eyg == MALE else '姨' + base
            return '叔' + base if eyg == MALE else '姑' + base
        return ''
    # ---- 配偶的伯叔姑舅姨及更上（P^k + E/Y）----
    if len(rest) >= 2 and isinstance(rest[0], Parent) \
            and all(isinstance(g, Parent) for g in rest[:-1]) \
            and isinstance(rest[-1], (Elder, Younger)):
        pp = rest[:-1]
        fg = pp[-1].gender
        ey = 'E' if isinstance(rest[-1], Elder) else 'Y'
        eyg = rest[-1].gender
        gen = s + len(pp)
        if gen == 0:
            flav = ('叔' if fg == MALE else '舅') if eyg == MALE else ('姑' if fg == MALE else '姨')
            return flav + ('姊' if ey == 'E' and eyg == FEMALE else SIB_F[ey][eyg]), \
                [flav + ('兄弟' if eyg == MALE else '姊妹')]
        if gen == -1:
            flav = ('叔' if fg == MALE else '舅') if eyg == MALE else ('姑' if fg == MALE else '姨')
            return flav + ('男' if eyg == MALE else '女'), []
        if gen <= -2:
            return _formal_descendant_at(gen, eyg), []
        if gen == 1:
            table = {(MALE, 'E', MALE): '伯父', (MALE, 'Y', MALE): '叔父',
                     (MALE, 'E', FEMALE): '姑母', (MALE, 'Y', FEMALE): '姑母',
                     (FEMALE, 'E', MALE): '舅父', (FEMALE, 'Y', MALE): '舅父',
                     (FEMALE, 'E', FEMALE): '姨母', (FEMALE, 'Y', FEMALE): '姨母'}
            return table[(fg, ey, eyg)], []
        if gen == 2:
            if fg == MALE:
                flav = ('伯' if ey == 'E' else '叔') if eyg == MALE else '姑'
            else:
                flav = '舅' if eyg == MALE else '姨'
            outer = '外' if ((s >= 1 and mate_g == FEMALE)
                             or (s == 0 and pp[0].gender == FEMALE)) else ''
            return flav + outer + ('祖父' if eyg == MALE else '祖母'), []
        if gen >= 3:
            flav = ('伯' if ey == 'E' and eyg == MALE and fg == MALE else
                    '叔' if fg == MALE and eyg == MALE else
                    '姑' if fg == MALE else
                    '舅' if eyg == MALE else '姨')
            # 目标在绝对辈分 gen 上：性别序列长度必须为 gen。
            # s>=1 时配偶及未知的 s-1 代用 mate_g/男补足；s<=0 时取 pp 的末 gen 代。
            if s >= 1:
                seq = [mate_g] + [MALE] * (s - 1) + [g.gender for g in pp]
            else:
                seq = [g.gender for g in pp][-gen:]
            seq = seq[:-1] + [eyg]
            return flav + _formal_ancestor(seq), []
        return ''
    # ---- 配偶兄弟姐妹的子女（E/Y + C^j）----
    if isinstance(rest[0], (Elder, Younger)) \
            and all(isinstance(g, Child) for g in rest[1:]):
        ey = 'E' if isinstance(rest[0], Elder) else 'Y'
        eyg = rest[0].gender
        cg = rest[-1].gender
        j = len(rest) - 1
        gen = s - j
        if gen == 0:
            if mate_g == FEMALE:
                line = '舅表' if eyg == MALE else '姨表'
            else:
                line = '叔表' if eyg == MALE else '姑表'
            if cg == MALE:
                return line + '兄', [line + '弟', line + '兄弟']
            return line + '姊', [line + '妹', line + '姐妹']
        if gen == 1:
            if mate_g == FEMALE:
                if cg == MALE:
                    return '舅表伯父' if eyg == MALE else '姨表伯父'
                return '舅表姑母' if eyg == MALE else '姨表姑母'
            if cg == MALE:
                return '堂伯父' if eyg == MALE else '堂姑丈'
            return '堂姑母'
        if s == 0:
            # 锚为同辈（嫂子/姐夫）：其兄弟之子女以 侄/甥 称
            stem = '侄' if eyg == MALE else '甥'
            if j == 1:
                return stem + ('男' if cg == MALE else '女'), []
            return stem + _formal_descendant([g.gender for g in rest[1:]]), []
        if gen == -1:
            return '男' if cg == MALE else '女'
        if gen <= -2:
            seq = [eyg] + [g.gender for g in rest[1:]]
            desc = _formal_descendant_seq_at(gen, seq)
            return desc, [desc + '男'] if cg == MALE else []
        if gen >= 2:
            line = ('舅表' if mate_g == FEMALE else '叔表') if eyg == MALE \
                else ('姨表' if mate_g == FEMALE else '姑表')
            lv = _formal_ancestor([MALE] * gen)[:-1]           # 祖/曾祖…（目标在第 gen 代）
            if cg == MALE:
                return line + '伯叔' + lv + '父', \
                    [line + '伯' + lv + '父', line + '叔' + lv + '父']
            return line + '姑' + lv + '母', []
        return ''
    # ---- 配偶伯叔姑舅姨的子女（P + E/Y + C^j）----
    if len(rest) >= 3 and isinstance(rest[0], Parent) \
            and isinstance(rest[1], (Elder, Younger)) \
            and all(isinstance(g, Child) for g in rest[2:]):
        fg = rest[0].gender
        ey = 'E' if isinstance(rest[1], Elder) else 'Y'
        eyg = rest[1].gender
        cg = rest[-1].gender
        gen = s + 1 - (len(rest) - 2)
        if gen == 0:
            line = {(MALE, MALE): '叔表', (MALE, FEMALE): '姑表',
                    (FEMALE, MALE): '舅表', (FEMALE, FEMALE): '姨'}[(fg, eyg)]
            if cg == MALE:
                return line + '兄', [line + '弟', line + '兄弟']
            return line + '姊', [line + '妹', line + '姐妹']
        if gen == -1:
            flav = ('叔' if fg == MALE else '舅') if eyg == MALE else ('姑' if fg == MALE else '姨')
            return flav + ('男' if cg == MALE else '女')
        if gen <= -2:
            seq = [eyg] + [g.gender for g in rest[2:]]
            return _formal_descendant_seq_at(gen, seq)
        if gen == 1:
            if mate_g == FEMALE:
                return '堂舅父' if cg == MALE else '堂姨母'
            if cg == MALE:
                return ('堂伯父' if ey == 'E' else '堂叔父')
            return '堂姑母'
        if gen >= 2:
            line = {(MALE, MALE): '叔表', (MALE, FEMALE): '姑表',
                    (FEMALE, MALE): '舅表', (FEMALE, FEMALE): '姨表'}[(fg, eyg)]
            lv = _formal_ancestor([MALE] * gen)[:-1]
            if cg == MALE:
                return line + '伯叔' + lv + '父', \
                    [line + '伯' + lv + '父', line + '叔' + lv + '父']
            return line + '姑' + lv + '母', []
        return ''
    return ''


def name_mate_middle(gens, i, mg):
    X = gens[:i]
    Y = gens[i + 1:]
    # 亲家（主表词形）
    if len(X) == 1 and isinstance(X[0], Child) and len(Y) == 1 \
            and isinstance(Y[0], Parent):
        return ('亲家公' if Y[0].gender == MALE else '亲家母'), []
    # 姻侄/姻侄女/姻侄孙…（主表词形）
    if len(X) == 1 and isinstance(X[0], Child) and Y \
            and isinstance(Y[0], (Elder, Younger)) \
            and all(isinstance(g, Child) for g in Y[1:]):
        if len(Y) == 1:
            return ('姻侄' if Y[0].gender == MALE else '姻侄女'), []
        desc = _formal_descendant([Y[0].gender] + [g.gender for g in Y[1:]])
        return '姻侄' + desc, []
    # 姻侄媳/姻侄婿（主表词形）
    if len(X) == 1 and isinstance(X[0], Child) and len(Y) == 2 \
            and isinstance(Y[0], (Elder, Younger)) and isinstance(Y[1], Mate):
        return ('姻侄媳' if Y[1].gender == FEMALE else '姻侄婿'), []
    # 姻/眷 体系
    s = priority(KinMonomial(X))
    seg = _inlaw_segment_prefix(X, mg)
    rname = _inlaw_rest_name(mg, s, Y)
    if seg and rname:
        if isinstance(rname, tuple):
            return seg + rname[0], [seg + a for a in rname[1]]
        return seg + rname, []
    # 兜底：以"段词干 + 眷/姻 + 重锚"表达（A之B 不再出现）
    prim_x, _ = name_mate_last(mg, X)
    stem = prim_x
    for suf in ('媳妇', '女婿', '之夫', '之妻'):
        if stem.endswith(suf):
            stem = stem[:-len(suf)]
            break
    else:
        for suf in ('妻', '夫', '妇', '媳', '婿', '嫂'):
            if stem.endswith(suf):
                stem = stem[:-1]
                break
    prefix = stem + ('眷' if mg == FEMALE else '姻')
    # 优先用重锚名（已经是目标的绝对辈分）
    if rname:
        if isinstance(rname, tuple):
            return prefix + rname[0], [prefix + a for a in rname[1]]
        return prefix + rname, []
    # 最后兜底：按 s + Y 的辈分取通用词，保证辈分/性别不再错位
    tg = s + priority(KinMonomial(Y))
    return prefix + _term_at_generation(tg, Y[-1].gender), []


# ----------------------------------------------------------------------------
# 主递归：对已化简单项式命名
# ----------------------------------------------------------------------------

def name_km(gens):
    """对已化简的单项式生成元序列命名，返回 (主呼称, 备选呼称列表)。"""
    if not gens:
        return '自己', []
    if len(gens) == 1:
        g = gens[0]
        if isinstance(g, Identity):
            return '自己', []
        if isinstance(g, Zero):
            return '无', []
        if isinstance(g, Parent):
            return PARENT[g.gender], PARENT_ALTS[g.gender]
        if isinstance(g, Child):
            return CHILD[g.gender], CHILD_ALTS[g.gender]
        if isinstance(g, Mate):
            return SPOUSE[g.gender], SPOUSE_ALTS[g.gender]
        if isinstance(g, (Elder, Younger)):
            ey = 'E' if isinstance(g, Elder) else 'Y'
            return SIB[ey][g.gender], SIB_ALTS[ey][g.gender]
    for g in gens:
        if g.gender is None:
            raise ValueError(
                "Genderless Generator Unsupported. Make Sure Every Generator "
                f"Has Gender == 'f' or 'm'. Your input: "
                + ''.join(x.tag for x in gens))
    # 直系
    if all(isinstance(g, Parent) for g in gens):
        return name_ancestors([g.gender for g in gens])
    if all(isinstance(g, Child) for g in gens):
        return name_descendants([g.gender for g in gens])
    # 含配偶
    mpos = [i for i, g in enumerate(gens) if isinstance(g, Mate)]
    if mpos:
        if mpos[-1] == len(gens) - 1:
            return name_mate_last(gens[-1].gender, gens[:-1])
        if mpos[0] == 0:
            return name_mate_first(gens[0].gender, gens[1:])
        i = mpos[0]
        return name_mate_middle(gens, i, gens[i].gender)
    # 纯旁系（无配偶）：E/Y 或 P* E/Y C*
    if isinstance(gens[0], (Elder, Younger)):
        ey = 'E' if isinstance(gens[0], Elder) else 'Y'
        return name_sibling_line(ey, gens[0].gender, gens[1:])
    k = 0
    while k < len(gens) and isinstance(gens[k], Parent):
        k += 1
    ey_gen = gens[k]
    ey = 'E' if isinstance(ey_gen, Elder) else 'Y'
    rest = gens[k + 1:]
    if not rest:
        return name_uncle(list(gens[:k]), ey, ey_gen.gender)
    return name_cousin_line(list(gens[:k]), ey, ey_gen.gender, rest)


# ----------------------------------------------------------------------------
# 公共接口
# ----------------------------------------------------------------------------

def naming_full(formula):
    """返回结构化命名结果列表。"""
    if isinstance(formula, KinPolynomial):
        out = []
        for km in formula.kin_monomial_list:
            if km.is_zero:
                continue
            prim, alts = name_km(km.generator_list)
            alts = [x for x in _alt_combine(prim, alts) if x != prim]
            entry = {'monomial': km.expression, 'primary': prim,
                     'alternatives': alts}
            if entry not in out:
                out.append(entry)
        return out
    if isinstance(formula, KinMonomial):
        if formula.is_zero:
            return []
        prim, alts = name_km(formula.generator_list)
        alts = [x for x in _alt_combine(prim, alts) if x != prim]
        return [{'monomial': formula.expression, 'primary': prim,
                 'alternatives': alts}]
    raise TypeError('naming() expects KinMonomial or KinPolynomial.')


def naming(formula):
    """KinMonomial -> 主呼称；KinPolynomial -> 主呼称列表（去重）。"""
    entries = naming_full(formula)
    primaries = []
    for e in entries:
        if e['primary'] not in primaries:
            primaries.append(e['primary'])
    return primaries[0] if isinstance(formula, KinMonomial) else primaries


# ----------------------------------------------------------------------------
# 从原始链命名（含同性婚姻 / 继亲标注）
# ----------------------------------------------------------------------------

CHAIN_HAN = {Parent: {MALE: '父', FEMALE: '母'}, Child: {MALE: '子', FEMALE: '女'},
             Mate: {MALE: '夫', FEMALE: '妻'}, Elder: {MALE: '兄', FEMALE: '姐'},
             Younger: {MALE: '弟', FEMALE: '妹'}, Identity: {None: '己'}}


def chain_to_text(gens):
    parts = []
    for g in gens:
        if isinstance(g, Identity):
            parts.append('己')
        elif isinstance(g, Zero):
            parts.append('0')
        else:
            parts.append(CHAIN_HAN[type(g)][g.gender])
    return '的'.join(parts)


def name_chain(gens):
    """从原始生成元链计算关系并命名。

    返回 dict：
      chain   原始链的中文表达
      formula 化简后的公式表达式
      names   [{monomial, primary, alternatives}, ...]
      primary 主呼称（多个可能时以 / 分隔）
      notes   备注（同性婚姻、继亲等）
    """
    notes = []
    # —— 化简前的结构探测：同性双亲 / 继亲 / 配偶之配偶 ——
    for i in range(len(gens) - 1):
        a, b = gens[i], gens[i + 1]
        if isinstance(a, Parent) and isinstance(b, Mate):
            if a.gender == b.gender:
                notes.append('同性婚姻：%s之%s（两位%s，与生身父母同称）' % (
                    '母' if a.gender == FEMALE else '父',
                    '妻' if b.gender == FEMALE else '夫',
                    '妈妈' if a.gender == FEMALE else '爸爸'))
            else:
                notes.append('%s之%s即%s（若非生身父母亦可称继%s）' % (
                    '母' if a.gender == FEMALE else '父',
                    '妻' if b.gender == FEMALE else '夫',
                    '妈妈' if b.gender == FEMALE else '爸爸',
                    '母' if b.gender == FEMALE else '父'))
        elif isinstance(a, Mate) and isinstance(b, Child):
            notes.append('%s之%s即亲生%s（若非亲生亦可称继%s）' % (
                '妻' if a.gender == FEMALE else '夫',
                '女' if b.gender == FEMALE else '子',
                '女儿' if b.gender == FEMALE else '儿子',
                '女' if b.gender == FEMALE else '子'))
        elif isinstance(a, Mate) and isinstance(b, Mate):
            notes.append('配偶之配偶即自己')
    formula = init(list(gens))
    entries = naming_full(formula)
    if not entries and formula.is_zero:
        return {'chain': chain_to_text(gens), 'formula': repr(formula),
                'names': [], 'primary': '无（此关系不成立）',
                'notes': ['关系链化简为 0：链路内的性别相互矛盾，此关系不成立。']}
    primary = ' / '.join(dict.fromkeys(e['primary'] for e in entries))
    return {'chain': chain_to_text(gens), 'formula': repr(formula),
            'names': entries, 'primary': primary, 'notes': notes}


# ----------------------------------------------------------------------------
# 关系转换：任意两人之间的呼称（A 对 B 怎么称呼）
# ----------------------------------------------------------------------------

_INV_CLASS = {'P': Child, 'C': Parent, 'E': Younger, 'Y': Elder, 'M': Mate}


def invert_gens(gens, ego_gender):
    """链的逆：gens 为"我→某人"的生成元链；返回"某人→我"的链。

    每个生成元取反（P↔C、E↔Y、M 不变），性别取"被描述者"的性别；
    第一个（离"某人"最近的）逆生成元描述的是"我"，其性别 = ego_gender。
    """
    inv = []
    for i in range(len(gens) - 1, -1, -1):
        g = gens[i]
        t = _INV_CLASS[type(g).__name__[0]]
        prev_g = ego_gender if i == 0 else gens[i - 1].gender
        inv.append(t(prev_g))
    return inv


def name_relate(chain_a, chain_b, ego_gender, gender_a=None):
    """A 对 B 的呼称。

    chain_a / chain_b：分别为"我→A"、"我→B"的生成元链（chain_a 空 = A 是我）。
    ego_gender：我的性别 'm'/'f'；None 表示未设置，此时按男/女两种可能
                分别计算并合并结果（dict 含 ambiguous 字段）。
    gender_a：A 的性别（A 链末位生成元的性别；A 是我时即 ego_gender），
              用于剔除"B 即 A 本人"分支中性别矛盾的项。

    返回 dict（同 name_chain；未设置性别时多一个 ambiguous 字段）。
    """
    if ego_gender in (MALE, FEMALE):
        return _name_relate_g(chain_a, chain_b, ego_gender, gender_a)
    r_m = _name_relate_g(chain_a, chain_b, MALE, gender_a)
    r_f = _name_relate_g(chain_a, chain_b, FEMALE, gender_a)
    entries = []
    seen = set()
    for e in r_m['names'] + r_f['names']:
        if e['primary'] in seen:
            continue
        seen.add(e['primary'])
        entries.append(e)
    notes = list(dict.fromkeys(r_m['notes'] + r_f['notes']))
    return {'chain': r_m['chain'], 'formula': r_m['formula'],
            'names': entries,
            'primary': ' / '.join(dict.fromkeys(e['primary'] for e in entries)),
            'notes': notes,
            'ambiguous': r_m['primary'] != r_f['primary']}


def _name_relate_g(chain_a, chain_b, ego_gender, gender_a):
    full = invert_gens(chain_a, ego_gender) + list(chain_b)
    formula = init(full)
    monos = [formula] if isinstance(formula, KinMonomial) else formula.kin_monomial_list
    entries = []
    seen = set()
    for km in monos:
        if km.is_zero:
            continue
        gs = km.generator_list
        # "B 即 A 本人"（I 分支）只有在我=A 且性别一致时才可能成立
        if len(gs) == 1 and isinstance(gs[0], Identity) \
                and gs[0].gender and gender_a and gs[0].gender != gender_a:
            continue
        prim, alts = name_km(gs)
        if prim in seen:
            continue
        seen.add(prim)
        entries.append({'monomial': km.expression, 'primary': prim,
                        'alternatives': [x for x in _alt_combine(prim, alts) if x != prim]})
    if not entries and formula.is_zero:
        return {'chain': chain_to_text(full), 'formula': repr(formula),
                'names': [], 'primary': '无（此关系不成立）', 'notes': []}
    return {'chain': chain_to_text(full), 'formula': repr(formula),
            'names': entries,
            'primary': ' / '.join(dict.fromkeys(e['primary'] for e in entries)),
            'notes': []}
