/* =========================================================================
 * kinship.js —— 亲属关系引擎 + 中文呼称命名（naming.py 的 JavaScript 移植）
 *
 * 生成元: {t: 'P'父|'C'子|'M'配偶|'E'兄/姐|'Y'弟/妹|'I'自己|'Z'无, g: 'm'|'f'|null}
 * 规则详见《命名规则.md》。可在浏览器与 Node.js 中运行。
 * ========================================================================= */
'use strict';

const M = 'm', F = 'f';

/* ----------------------------- 引擎：init ----------------------------- */

function transform(s1, s2) {
  if (s1.t === 'Z' || s2.t === 'Z') return [{ t: 'Z', g: null }];
  if (s2.t === 'I') {
    if (s2.g != null && s2.g !== s1.g) return [{ t: 'Z', g: null }];
    return [s1];
  }
  if (s1.t === 'I') return [s2];
  if (s1.t === 'P') {
    if (s2.t === 'C') return [{ t: 'E', g: s2.g }, { t: 'I', g: s2.g }, { t: 'Y', g: s2.g }];
    if (s2.t === 'M') return [{ t: 'P', g: s2.g }];
  } else if (s1.t === 'M') {
    if (s2.t === 'C') return [s2];
    if (s2.t === 'M') return [{ t: 'I', g: s2.g }];
  } else if (s1.t === 'C') {
    if (s2.t === 'P') return [{ t: 'M', g: s2.g }, { t: 'I', g: s2.g }];
    if (s2.t === 'E' || s2.t === 'Y') return [{ t: 'C', g: s2.g }];
  } else if (s1.t === 'E' || s1.t === 'Y') {
    if (s2.t === 'P') return [s2];
    if (s2.t === 'E' || s2.t === 'Y') {
      if (s1.t === s2.t) return [s2];
      return [{ t: 'E', g: s2.g }, { t: 'I', g: s2.g }, { t: 'Y', g: s2.g }];
    }
  }
  return null; // 无变换 → 直接拼接
}

function canPutIn(last, s) {
  if (last == null) return true;
  if ((last.t === 'P' || last.t === 'M') && (s.t === 'P' || s.t === 'E' || s.t === 'Y')) return true;
  if ((last.t === 'E' || last.t === 'Y' || last.t === 'C') && (s.t === 'C' || s.t === 'M')) return true;
  return false;
}

function tryToPutIn(term, s) {
  const last = term.length ? term[term.length - 1] : null;
  if (last == null || canPutIn(last, s)) {
    const t = term.slice();
    t.push(s);
    return [t];
  }
  const prev = term.slice(0, -1);
  const newOnes = transform(term[term.length - 1], s);
  const out = [];
  for (const one of newOnes) out.push(...tryToPutIn(prev, one));
  return out;
}

function init(gens) {
  if (!gens || gens.length === 0) return { monomials: [[{ t: 'I', g: null }]] };
  let results = [[]];
  for (const s of gens) {
    const next = [];
    for (const t of results) next.push(...tryToPutIn(t, s));
    results = next;
  }
  const seen = {};
  const monomials = [];
  for (const r of results) {
    const isZero = r.length === 1 && r[0].t === 'Z';
    if (isZero) continue;
    const key = r.map(x => x.t + (x.g || '')).join('');
    if (seen[key]) continue;
    seen[key] = true;
    monomials.push(r);
  }
  if (monomials.length === 0) return { monomials: [[{ t: 'Z', g: null }]] };
  return { monomials };
}

/* ------------------------------ 基础称谓表 ------------------------------ */

const PARENT = { m: '爸爸', f: '妈妈' };
const PARENT_ALTS = { m: ['父亲', '爸', '父'], f: ['母亲', '妈', '母'] };
const CHILD = { m: '儿子', f: '女儿' };
const CHILD_ALTS = { m: ['儿', '子'], f: ['女'] };
const SIB = { E: { m: '哥哥', f: '姐姐' }, Y: { m: '弟弟', f: '妹妹' } };
const SIB_F = { E: { m: '兄', f: '姊' }, Y: { m: '弟', f: '妹' } };
const SIB_ALTS = { E: { m: ['哥', '兄长'], f: ['姐'] }, Y: { m: ['弟'], f: ['妹'] } };
const SPOUSE = { m: '丈夫', f: '妻子' };
const SPOUSE_ALTS = { m: ['老公', '夫', '先生'], f: ['老婆', '妻', '太太'] };
// 世代前缀只保留"曾"：更深世代用 曾/外曾 长链直接写出（曾曾祖父、外曾曾外祖父…）

function formalAncestor(gs) {
  if (gs.length === 1) return gs[0] === 'm' ? '父' : '母';
  if (gs.length === 2) {
    const k = gs[0] + gs[1];
    return { mm: '祖父', mf: '祖母', fm: '外祖父', ff: '外祖母' }[k];
  }
  return nameAncestors(gs).primary;
}

function formalDescendant(gs) {
  if (gs.length === 1) return gs[0] === 'm' ? '子' : '女';
  if (gs.length === 2) {
    const k = gs[0] + gs[1];
    return { mm: '孙', mf: '孙女', fm: '外孙', ff: '外孙女' }[k];
  }
  return nameDescendants(gs).primary;
}

function formalDescendantAt(gen, gender) {
  if (gen > -2) throw new Error('formalDescendantAt expects gen <= -2');
  return formalDescendant(Array(-gen - 1).fill('m').concat([gender]));
}

function formalDescendantSeqAt(gen, seq) {
  if (gen > -2) throw new Error('formalDescendantSeqAt expects gen <= -2');
  const need = -gen;
  let s = seq.slice();
  if (s.length < need) s = Array(need - s.length).fill('m').concat(s);
  else s = s.slice(s.length - need);
  return formalDescendant(s);
}

function termAtGeneration(gen, gender) {
  if (gen === 0) return gender === 'm' ? '兄弟' : '姊妹';
  if (gen === -1) return gender === 'm' ? '男' : '女';
  if (gen <= -2) return formalDescendantAt(gen, gender);
  return formalAncestor(Array(gen - 1).fill('m').concat([gender]));
}

/* ------------------------------ 直系祖辈 ------------------------------ */

function nameAncestors(gs) {
  /* 逐代剥离（无碰撞）：n=1 父/母；n=2 祖父/祖母/外祖父/外祖母；
     n>=3：自"我"侧剥离——父链加"曾"，母链加"外曾"。 */
  const n = gs.length;
  if (n === 1) return { primary: PARENT[gs[0]], alts: PARENT_ALTS[gs[0]] };
  if (n === 2) {
    const t = { mm: ['爷爷', ['祖父']], mf: ['奶奶', ['祖母']], fm: ['外公', ['外祖父']], ff: ['外婆', ['外祖母']] }[gs[0] + gs[1]];
    return { primary: t[0], alts: t[1] };
  }
  let pref = '';
  const rest = gs.slice();
  while (rest.length > 2) {
    pref += rest[0] === 'm' ? '曾' : '外曾';
    rest.shift();
  }
  const base = { mm: '祖父', mf: '祖母', fm: '外祖父', ff: '外祖母' }[rest[0] + rest[1]];
  return { primary: pref + base, alts: [] };
}

/* ------------------------------ 直系晚辈 ------------------------------ */

function nameDescendants(gs) {
  /* 逐代剥离（无碰撞）：n=1 儿/女；n=2 孙子/孙女/外孙/外孙女；
     n>=3：自"我"侧剥离——子链加"曾"，女链加"外曾"（末尾不加"子"）。 */
  const n = gs.length;
  if (n === 1) return { primary: CHILD[gs[0]], alts: CHILD_ALTS[gs[0]] };
  if (n === 2) {
    if (gs[0] === 'm') return { primary: gs[1] === 'm' ? '孙子' : '孙女', alts: [] };
    return { primary: gs[1] === 'm' ? '外孙' : '外孙女', alts: [] };
  }
  let pref = '';
  const rest = gs.slice();
  while (rest.length > 2) {
    pref += rest[0] === 'm' ? '曾' : '外曾';
    rest.shift();
  }
  const base = (rest[0] === 'm' ? '孙' : '外孙') + (rest[1] === 'm' ? '' : '女');
  return { primary: pref + base, alts: [] };
}

/* ------------------------------ 叔伯姑舅姨 ------------------------------ */

const UNCLE1 = {
  'm,E,m': '伯父', 'm,Y,m': '叔叔', 'm,E,f': '大姑', 'm,Y,f': '小姑',
  'f,E,m': '大舅', 'f,Y,m': '小舅', 'f,E,f': '大姨', 'f,Y,f': '小姨'
};
const UNCLE1_GEN = { 'm,f': ['姑妈', '姑母', '姑姑'], 'f,m': ['舅舅', '舅父'], 'f,f': ['姨妈', '姨母'] };
const UNCLE2 = {
  'm,m,E,m': '伯公', 'm,m,Y,m': '叔公', 'm,m,E,f': '姑奶奶', 'm,m,Y,f': '姑奶奶',
  'm,f,E,m': '大舅爷', 'm,f,Y,m': '小舅爷', 'm,f,E,f': '姨奶奶', 'm,f,Y,f': '姨奶奶',
  'f,m,E,m': '伯外公', 'f,m,Y,m': '叔外公', 'f,m,E,f': '姑外婆', 'f,m,Y,f': '姑外婆',
  'f,f,E,m': '舅外公', 'f,f,Y,m': '舅外公', 'f,f,E,f': '姨外婆', 'f,f,Y,f': '姨外婆'
};
const UNCLE1_MATE = {
  'm,E,m': { f: ['伯母', []], m: ['伯婿', []] },
  'm,Y,m': { f: ['婶婶', ['叔母']], m: ['叔婿', []] },
  'm,E,f': { m: ['大姑丈', ['姑丈', '姑父']], f: ['大姑媳', ['姑媳']] },
  'm,Y,f': { m: ['小姑丈', ['姑丈', '姑父']], f: ['小姑媳', ['姑媳']] },
  'f,E,m': { f: ['大舅妈', ['舅妈', '舅母']], m: ['大舅婿', ['舅婿']] },
  'f,Y,m': { f: ['小舅妈', ['舅妈', '舅母']], m: ['小舅婿', ['舅婿']] },
  'f,E,f': { m: ['大姨丈', ['姨丈', '姨父']], f: ['大姨媳', ['姨媳']] },
  'f,Y,f': { m: ['小姨丈', ['姨丈', '姨父']], f: ['小姨媳', ['姨媳']] }
};
const UNCLE2_MATE = {
  'm,m,E,m': { f: '伯婆' }, 'm,m,Y,m': { f: '叔婆' },
  'm,m,E,f': { m: '姑爷爷' }, 'm,m,Y,f': { m: '姑爷爷' },
  'm,f,E,m': { f: '大舅婆' }, 'm,f,Y,m': { f: '小舅婆' },
  'm,f,E,f': { m: '姨爷爷' }, 'm,f,Y,f': { m: '姨爷爷' },
  'f,m,E,m': { f: '伯外婆' }, 'f,m,Y,m': { f: '叔外婆' },
  'f,m,E,f': { m: '姑外公' }, 'f,m,Y,f': { m: '姑外公' },
  'f,f,E,m': { f: '舅外婆' }, 'f,f,Y,m': { f: '舅外婆' },
  'f,f,E,f': { m: '姨外公' }, 'f,f,Y,f': { m: '姨外公' }
};

function mateUncleLine(pp, ey, eyg) {
  const last = pp[pp.length - 1].g;
  if (eyg === 'm') {
    if (last === 'm') return ey === 'E' ? '伯' : '叔';
    return '舅';
  }
  if (last === 'm') return '姑';
  return '姨';
}

function nameUncle(pp, ey, eyg) {
  const k = pp.length;
  if (k === 1) {
    return { primary: UNCLE1[pp[0].g + ',' + ey + ',' + eyg], alts: UNCLE1_GEN[pp[0].g + ',' + eyg] || [] };
  }
  if (k === 2) {
    const key = pp[0].g + ',' + pp[1].g + ',' + ey + ',' + eyg;
    const alts = (pp[0].g + ',' + pp[1].g + ',' + eyg) === 'm,f,m' ? ['舅爷爷'] : [];
    return { primary: UNCLE2[key], alts };
  }
  const anc = formalAncestor(pp.map(g => g.g)).slice(0, -1) + (eyg === 'm' ? '父' : '母');
  const line = mateUncleLine(pp, ey, eyg);
  // 备选名的末字必须与目标性别一致（不能给女性目标配"姑曾祖父"）
  const alts = [(eyg === 'm' ? '伯叔' : '姑') + anc];
  return { primary: line + anc, alts };
}

/* ------------------------------ 堂表亲 ------------------------------ */

function juniorRoleName(role, gender, cls) {
  if (role === 0) {
    if (gender === 'm') return { primary: cls + '兄弟', alts: [cls + '哥', cls + '弟'] };
    return { primary: cls + '姐妹', alts: [cls + '姐', cls + '妹'] };
  }
  if (role === -1) {
    if (gender === 'm') return { primary: cls + '伯叔父', alts: [cls + '伯', cls + '叔', cls + '伯父', cls + '叔父'] };
    return { primary: cls + '姑', alts: [] };
  }
  if (role <= -2) {
    const anc = formalAncestor(Array(-role).fill('m'));
    if (gender === 'm') return { primary: cls + '伯叔' + anc, alts: [cls + '伯' + anc, cls + '叔' + anc] };
    if (role === -2) return { primary: '姑祖母', alts: [cls + '姑祖母'] };
    return { primary: '曾'.repeat(-role - 2) + '姑祖母', alts: [cls + '姑'] };
  }
  if (role === 1) return { primary: cls + (gender === 'm' ? '侄' : '侄女'), alts: [] };
  if (role === 2) return { primary: cls + (gender === 'm' ? '侄孙' : '侄孙女'), alts: [] };
  const des = formalDescendant(Array(role - 1).fill('m').concat([gender]));
  return { primary: cls + '侄' + des, alts: [] };
}

function cousinClass(k, j) {
  if (j === 1) return '堂';
  if (k === 2) return '从堂';
  if (k === 3) return j === 2 ? '从' : '族';
  if (j === 2) return '从堂';
  if (j === 3) return '族';
  if (j === 4) return '四从父';
  return '族';
}

const COUSIN2_MALE = {
  'm,m,m': ['堂伯', '堂叔'], 'm,m,f': ['姑表伯父', '姑表叔父'],
  'm,f,m': ['舅表伯父', '舅表叔父'], 'm,f,f': ['姨伯父', '姨叔父'],
  'f,m,m': ['堂舅', '堂舅'], 'f,m,f': ['姑表舅父', '姑表舅父'],
  'f,f,m': ['舅表舅父', '舅表舅父'], 'f,f,f': ['姨舅父', '姨舅父']
};
const COUSIN2_FEMALE = {
  'm,m,m': ['堂姑', '堂姑'], 'm,m,f': ['姑表姑母', '姑表姑母'],
  'm,f,m': ['舅表姑母', '舅表姑母'], 'm,f,f': ['姨姑母', '姨姑母'],
  'f,m,m': ['堂姨', '堂姨'], 'f,m,f': ['姑表姨母', '姑表姨母'],
  'f,f,m': ['舅表姨母', '舅表姨母'], 'f,f,f': ['姨姨母', '姨姨母']
};
const K2_L0_CLASS = {
  'm,m,m,m': '从堂', 'm,m,m,f': '堂姑表',
  'm,m,f,m': '姑表叔表', 'm,m,f,f': '姑表姑表',
  'm,f,m,m': '舅表叔表', 'm,f,m,f': '舅表姑表',
  'm,f,f,m': '从母叔表', 'm,f,f,f': '从母姑表',
  'f,m,m,m': '堂舅表', 'f,m,m,f': '堂姨表',
  'f,m,f,m': '姑表舅表', 'f,m,f,f': '姑表姨表',
  'f,f,m,m': '舅表舅表', 'f,f,m,f': '舅表姨表',
  'f,f,f,m': '从母舅表', 'f,f,f,f': '再从母'
};

function nameCousinLine(pp, ey, eyg, rest) {
  const k = pp.length, j = rest.length, cg = rest[rest.length - 1].g, r = j - k;
  if (k === 1) {
    let cls;
    if (eyg === 'm' && pp[0].g === 'm') cls = '堂';
    else if (eyg === 'f' && pp[0].g === 'm') cls = '姑表';
    else if (eyg === 'm') cls = '舅表';
    else cls = '姨';
    if (r === 0) return juniorRoleName(0, cg, cls);
    if (j === 2) {
      if (rest[0].g === 'f') {
        return { primary: cls + '外甥' + (cg === 'm' ? '' : '女'), alts: [cls + '甥' + (cg === 'm' ? '男' : '女')] };
      }
      return { primary: cls + '侄' + (cg === 'm' ? '' : '女'), alts: [cls + '侄男'] };
    }
    const stem = rest[0].g === 'f' ? '甥' : '侄';
    if (j === 3) {
      const des = formalDescendant(rest.slice(1).map(x => x.g));
      return { primary: cls + stem + des, alts: cg === 'm' ? [cls + stem + des + '男'] : [] };
    }
    const des = formalDescendant(rest.slice(1).map(x => x.g));
    if (rest[0].g === 'm') return { primary: cls + des, alts: [] };
    return { primary: cls + '甥' + des, alts: [] };
  }
  if (k === 2) {
    const key = pp[0].g + ',' + pp[1].g + ',' + eyg;
    if (j === 1) {
      if (cg === 'm') {
        const t = COUSIN2_MALE[key];
        return { primary: t[0], alts: [t[1]] };
      }
      const t = COUSIN2_FEMALE[key];
      return { primary: t[0], alts: [t[1]] };
    }
    const cls = K2_L0_CLASS[pp[0].g + ',' + pp[1].g + ',' + eyg + ',' + rest[0].g];
    if (j === 2) return juniorRoleName(0, cg, cls);
    if (j === 3) {
      return { primary: cls + (cg === 'm' ? '侄' : '侄女'), alts: cg === 'm' ? [cls + '侄男'] : [] };
    }
    const des = formalDescendant(rest.slice(2).map(x => x.g));
    return { primary: cls + '侄' + des, alts: [] };
  }
  if (k >= 3 && j === 1) {
    const line1 = { 'm,m': '堂', 'm,f': '姑表', 'f,m': '舅表', 'f,f': '姨' }[pp[pp.length - 1].g + ',' + eyg];
    const outer = pp[0].g === 'f' ? '外' : '';
    let base;
    if (k === 3) base = outer + (cg === 'm' ? '祖父' : '祖母');
    else if (k === 4) base = outer + (cg === 'm' ? '曾祖父' : '曾祖母');
    else base = outer + formalAncestor(Array(k - 1).fill('m')).slice(0, -1) + (cg === 'm' ? '父' : '母');
    if (cg === 'm' && pp[pp.length - 2].g === 'm') {
      return { primary: line1 + '伯叔' + base, alts: [line1 + '伯' + base, line1 + '叔' + base] };
    }
    const line2 = cg === 'm' ? (pp[pp.length - 2].g === 'f' ? '舅' : '伯叔') : (pp[pp.length - 2].g === 'f' ? '姨' : '姑');
    return { primary: line1 + line2 + base, alts: [] };
  }
  if (!pp.every(g => g.g === 'm') || eyg === 'f') {
    // 线1（最近祖先×旁系性别）+ 每代一个线2' + 角色（次近祖先×末代性别）
    const LINE1 = { 'm,m': '堂', 'm,f': '姑表', 'f,m': '舅表', 'f,f': '从母' };
    const LINE2 = { 'm,m': '叔表', 'm,f': '姑表', 'f,m': '舅表', 'f,f': '姨表' };
    const ROLE2 = { 'm,m': '伯叔', 'm,f': '姑', 'f,m': '舅', 'f,f': '姨' };
    let cls = LINE1[pp[pp.length - 1].g + ',' + eyg] + LINE2[pp[pp.length - 2].g + ',' + rest[0].g];
    for (let d = 2; d < j; d++) cls += LINE2[rest[d - 2].g + ',' + rest[d - 1].g];
    const r = j - k;
    if (r === 0) return juniorRoleName(0, cg, cls);
    if (r === -1) {
      const role = ROLE2[pp[pp.length - 2].g + ',' + cg] + (cg === 'm' ? '父' : '母');
      if (cg === 'm' && pp[pp.length - 2].g === 'm') {
        return { primary: cls + role, alts: [cls + '伯父', cls + '叔父'] };
      }
      return { primary: cls + role, alts: [] };
    }
    if (r <= -2) {
      const lv = formalAncestor(Array(-r).fill('m')).slice(0, -1);
      const role = ROLE2[pp[pp.length - 2].g + ',' + cg] + lv + (cg === 'm' ? '父' : '母');
      if (cg === 'm' && pp[pp.length - 2].g === 'm') {
        return { primary: cls + role, alts: [cls + '伯' + lv + '父', cls + '叔' + lv + '父'] };
      }
      return { primary: cls + role, alts: [] };
    }
    if (r === 1) {
      return { primary: cls + (cg === 'm' ? '侄' : '侄女'), alts: cg === 'm' ? [cls + '侄男'] : [] };
    }
    if (r === 2) {
      return { primary: cls + (cg === 'm' ? '侄孙' : '侄孙女'), alts: cg === 'm' ? [cls + '侄孙男'] : [] };
    }
    const des = formalDescendant(Array(r - 1).fill('m').concat([cg]));
    return { primary: cls + '侄' + des, alts: [] };
  }
  return juniorRoleName(r, cg, cousinClass(k, j));
}

function nameCousinMate(pp, ey, eyg, rest, mg) {
  const k = pp.length, j = rest.length, cg = rest[rest.length - 1].g, r = j - k;
  if (k === 1 && r === 0) {
    let cls;
    if (pp[0].g === 'm' && eyg === 'm') cls = '堂';
    else if (pp[0].g === 'm') cls = '姑表';
    else if (eyg === 'm') cls = '舅表';
    else cls = '姨';
    if (cg === 'm') {
      return mg === 'f' ? { primary: cls + '嫂', alts: [cls + '弟媳'] } : { primary: cls + '兄婿', alts: [cls + '弟婿'] };
    }
    return mg === 'm' ? { primary: cls + '姐夫', alts: [cls + '妹夫'] } : { primary: cls + '姐嫂', alts: [cls + '妹媳'] };
  }
  if (k === 2 && j === 1) {
    const key = pp[0].g + ',' + pp[1].g + ',' + eyg;
    if (cg === 'm') {
      const t = COUSIN2_MALE[key];
      if (mg === 'f') {
        if (key === 'm,m,m') return { primary: '堂伯母', alts: ['堂婶'] };
        if (t[0] === '堂舅') return { primary: '堂舅妈', alts: [] };
        return { primary: t[0].slice(0, -1) + '母', alts: [t[1].slice(0, -1) + '母'] };
      }
      return { primary: t[0] + '婿', alts: [t[1] + '婿'] };
    }
    const t = COUSIN2_FEMALE[key];
    if (mg === 'm') {
      if (t[0] === '堂姑') return { primary: '堂姑丈', alts: [] };
      if (t[0] === '堂姨') return { primary: '堂姨丈', alts: [] };
      return { primary: t[0].slice(0, -1) + '父', alts: [] };
    }
    return { primary: t[0].replace(/母$/, '') + '媳', alts: [] };
  }
  const primRes = nameCousinLine(pp, ey, eyg, rest);
  const prim = primRes.primary, alts = primRes.alts;
  if (r === 0) {
    if (cg === 'm') {
      return mg === 'f'
        ? { primary: prim.slice(0, -2) + '嫂', alts: [prim.slice(0, -2) + '弟媳'] }
        : { primary: prim.slice(0, -2) + '兄婿', alts: [prim.slice(0, -2) + '弟婿'] };
    }
    return mg === 'm'
      ? { primary: prim.slice(0, -2) + '姐夫', alts: [prim.slice(0, -2) + '妹夫'] }
      : { primary: prim.slice(0, -2) + '姐嫂', alts: [prim.slice(0, -2) + '妹媳'] };
  }
  if (prim.endsWith('父')) {
    const sw = a => a.slice(0, -1) + (mg === 'm' ? '父' : '母');
    return { primary: sw(prim), alts: alts.map(sw) };
  }
  if (prim.endsWith('母')) {
    return { primary: prim.slice(0, -1) + (mg === 'm' ? '父' : '母'), alts: [] };
  }
  if (prim.endsWith('女')) {
    const keep = prim + (mg === 'm' ? '婿' : '媳');
    const a2 = [prim.slice(0, -1) + (mg === 'm' ? '婿' : '媳')];
    if (prim.indexOf('外甥') >= 0) a2.push(prim.replace('外甥', '甥').slice(0, -1) + (mg === 'm' ? '婿' : '媳'));
    return { primary: keep, alts: a2 };
  }
  if (mg === 'f') {
    if (prim.startsWith('堂') || /(孙|曾孙|玄孙|来孙|晜孙)$/.test(prim)) {
      return { primary: prim + '媳妇', alts: [prim + '妇'] };
    }
    const base = prim.indexOf('外甥') >= 0 ? prim.replace('外甥', '甥') : prim;
    return { primary: base + '妇', alts: [prim + '妇', prim + '媳妇'] };
  }
  return { primary: prim + '婿', alts: [] };
}

/* ------------------------------ 兄弟姐妹 / 侄甥 ------------------------------ */

function nameSiblingLine(ey, eyg, rest) {
  if (!rest.length) return { primary: SIB[ey][eyg], alts: SIB_ALTS[ey][eyg] };
  const j = rest.length, cg = rest[rest.length - 1].g;
  if (j === 1) {
    if (eyg === 'm') return { primary: '侄' + (cg === 'm' ? '子' : '女'), alts: [] };
    return { primary: '外甥' + (cg === 'm' ? '' : '女'), alts: [] };
  }
  const core = eyg === 'm' ? '侄' : '甥';
  const des = formalDescendant(rest.map(g => g.g));
  return { primary: core + des, alts: [] };
}

function nameSiblingMate(ey, eyg, mg) {
  const t = {
    'E,m': { f: ['嫂子', []], m: ['兄婿', []] },
    'Y,m': { f: ['弟媳', ['弟妹']], m: ['弟婿', []] },
    'E,f': { m: ['姐夫', []], f: ['姐嫂', []] },
    'Y,f': { m: ['妹夫', []], f: ['妹媳', []] }
  }[ey + ',' + eyg][mg];
  return { primary: t[0], alts: t[1] };
}

function nameNephewMate(ey, eyg, rest, mg) {
  const j = rest.length, cg = rest[rest.length - 1].g;
  const core = eyg === 'm' ? '侄' : '甥';
  if (j === 1) {
    if (cg === 'm') {
      return mg === 'f' ? { primary: core + '媳妇', alts: [core + '媳'] } : { primary: core + '婿', alts: [] };
    }
    return mg === 'm' ? { primary: core + '女婿', alts: [] } : { primary: core + '女媳', alts: [] };
  }
  const base = core + formalDescendant(rest.map(g => g.g));
  if (base.endsWith('女')) {
    return mg === 'm' ? { primary: base.slice(0, -1) + '婿', alts: [] } : { primary: base + '媳', alts: [] };
  }
  return mg === 'f' ? { primary: base + '妇', alts: [] } : { primary: base + '婿', alts: [] };
}

/* ------------------------------ 姻亲 ------------------------------ */

const MATE_PARENT = { 'f,m': '岳父', 'f,f': '岳母', 'm,m': '公公', 'm,f': '婆婆' };
const MATE_SIB = {
  'f,E,m': '大舅子', 'f,Y,m': '小舅子', 'f,E,f': '大姨子', 'f,Y,f': '小姨子',
  'm,E,m': '大伯子', 'm,Y,m': '小叔子', 'm,E,f': '大姑子', 'm,Y,f': '小姑子'
};
const MATE_SIB_GEN = { 'm,f': ['姑子', '夫姑'], 'f,m': ['舅子', '妻舅'], 'f,f': ['姨子', '妻姨'] };
const MATE_SIB_MATE = {
  'f,E,m': { f: '大舅妇', m: '大舅子婿' }, 'f,Y,m': { f: '小舅妇', m: '小舅子婿' },
  'f,E,f': { m: '大姨夫', f: '大姨子媳' }, 'f,Y,f': { m: '小姨夫', f: '小姨子媳' },
  'm,E,m': { f: '大婶子', m: '大伯子婿' }, 'm,Y,m': { f: '小婶子', m: '小叔子婿' },
  'm,E,f': { m: '大姑夫', f: '大姑子媳' }, 'm,Y,f': { m: '小姑夫', f: '小姑子媳' }
};
const MATE_NEPHEW = {
  'f,m,m': ['舅侄', ['内侄', '妻侄子']], 'f,m,f': ['舅侄女', ['内侄女', '妻侄女']],
  'f,f,m': ['姨甥', ['妻甥男']], 'f,f,f': ['姨甥女', ['妻甥女']],
  'm,m,m': ['叔侄', ['夫侄子']], 'm,m,f': ['叔侄女', ['夫侄女']],
  'm,f,m': ['姑甥', ['夫甥男']], 'm,f,f': ['姑甥女', ['夫甥女']]
};
const MATE_UNCLE1 = {
  'f,m,E,m': '伯岳父', 'f,m,Y,m': '叔岳父', 'f,m,E,f': '姑岳母', 'f,m,Y,f': '姑岳母',
  'f,f,E,m': '舅岳父', 'f,f,Y,m': '舅岳父', 'f,f,E,f': '姨岳母', 'f,f,Y,f': '姨岳母',
  'm,m,E,m': '伯公父', 'm,m,Y,m': '叔公父', 'm,m,E,f': '姑婆母', 'm,m,Y,f': '姑婆母',
  'm,f,E,m': '舅公父', 'm,f,Y,m': '舅公父', 'm,f,E,f': '姨婆母', 'm,f,Y,f': '姨婆母'
};

function mateSibMateNames(mg, ey, eyg, m2) {
  const big = MATE_SIB_MATE[mg + ',' + 'E' + ',' + eyg][m2];
  const small = MATE_SIB_MATE[mg + ',' + 'Y' + ',' + eyg][m2];
  const alts = [small];
  if (mg === 'f' && eyg === 'm' && m2 === 'f') alts.push('大舅嫂', '小舅嫂', '舅嫂');
  if (mg === 'm' && eyg === 'f' && m2 === 'm') alts.push('姑夫');
  if (mg === 'm' && eyg === 'm' && m2 === 'f') alts.push('妯娌');
  if (mg === 'f' && eyg === 'f' && m2 === 'm') alts.push('连襟');
  return { primary: MATE_SIB_MATE[mg + ',' + ey + ',' + eyg][m2], alts };
}

function mateAncestorInsert(base, mg) {
  if (!/[\u7236\u6bcd\u7956]$/.test(base)) return base;
  if (mg === 'f') return base.slice(0, -1) + '岳' + base.slice(-1);
  if (base.endsWith('父')) return base.slice(0, -1) + '公父';
  if (base.endsWith('母')) return base.slice(0, -1) + '婆母';
  return base.slice(0, -1) + '公' + base.slice(-1);
}

/* 眷/姻 段前缀 */
function inlawSegmentPrefix(X, mg) {
  const n = X.length;
  const suf = mg === 'f' ? '眷' : '姻';
  if (n === 1) {
    const x = X[0];
    if (x.t === 'C') return (x.g === 'm' ? '男' : '女') + suf;
    if (x.t === 'E' || x.t === 'Y') return (x.g === 'm' ? '兄弟' : '姊妹') + suf;
    return null;
  }
  if (n === 2) {
    const a = X[0], b = X[1];
    if (a.t === 'C' && b.t === 'C') return (a.g === 'm' ? '孙' : '外孙') + suf;
    if ((a.t === 'E' || a.t === 'Y') && b.t === 'C') return (a.g === 'm' ? '侄' : '甥') + suf;
    if (a.t === 'P' && (b.t === 'E' || b.t === 'Y')) {
      const base = { 'm,m': '叔', 'f,m': '舅', 'm,f': '姑', 'f,f': '姨' }[a.g + ',' + b.g];
      return base + suf;
    }
    if (a.t === 'M' && (b.t === 'E' || b.t === 'Y')) {
      const base = { 'm,m': '叔兄弟', 'f,m': '舅兄弟', 'm,f': '姑姊妹', 'f,f': '姨姊妹' }[a.g + ',' + b.g];
      return base + suf;
    }
    return null;
  }
  if (n === 3 && X[0].t === 'P' && X[1].t === 'P' && (X[2].t === 'E' || X[2].t === 'Y')) {
    const key = X[0].g + ',' + X[1].g + ',' + X[2].g;
    const base = {
      'm,m,m': '叔祖', 'm,m,f': '姑祖', 'm,f,m': '舅祖', 'm,f,f': '姨祖',
      'f,m,m': '叔外祖', 'f,m,f': '姑外祖', 'f,f,m': '舅外祖', 'f,f,f': '姨外祖'
    }[key];
    return base + suf;
  }
  if (n >= 3 && X[0].t === 'P' && (X[1].t === 'E' || X[1].t === 'Y') && X.slice(2).every(x => x.t === 'C')) {
    const g1 = X[0].g, eyg = X[1].g;
    const j = n - 2;
    if (j === 1) {
      const t = {
        'm,m': mg === 'f' ? '从父兄弟眷' : '从父姊妹姻', 'm,f': mg === 'f' ? '姑表兄弟眷' : '姑表姊妹姻',
        'f,m': mg === 'f' ? '舅表兄弟眷' : '舅表姊妹姻', 'f,f': mg === 'f' ? '从母兄弟眷' : '从母姊妹姻'
      };
      return t[g1 + ',' + eyg] || null;
    }
    const cls = { 'm,m': '堂', 'm,f': '姑表', 'f,m': '舅表', 'f,f': '姨' }[g1 + ',' + eyg];
    const cg = X[X.length - 1].g;
    const suf = mg === 'f' ? '眷' : '姻';
    if (j === 2) {
      const stem = X[2].g === 'f' ? '甥' : '侄';
      return cls + stem + suf;
    }
    const des = formalDescendant(Array(j - 2).fill('m').concat([cg]));
    return cls + '侄' + des + suf;
  }
  if (n >= 4 && X[0].t === 'P' && X[1].t === 'P' && (X[2].t === 'E' || X[2].t === 'Y') && X.slice(3).every(x => x.t === 'C')) {
    const g1 = X[0].g, g2 = X[1].g, eyg = X[2].g;
    const j = n - 3;
    if (j === 1) {
      const t = {
        'm,m,m': mg === 'f' ? '从父叔眷' : '从父姑姻', 'm,m,f': mg === 'f' ? '姑表叔眷' : '姑表姑姻',
        'm,f,m': mg === 'f' ? '舅表叔眷' : '舅表姑姻', 'm,f,f': mg === 'f' ? '从母叔眷' : '从母姑姻',
        'f,m,m': mg === 'f' ? '从父舅眷' : '从父姨姻', 'f,m,f': mg === 'f' ? '姑表舅眷' : '姑表姨姻',
        'f,f,m': mg === 'f' ? '舅表舅眷' : '舅表姨姻', 'f,f,f': mg === 'f' ? '从母舅眷' : '从母姨姻'
      };
      return t[g1 + ',' + g2 + ',' + eyg] || null;
    }
    const cls = K2_L0_CLASS[g1 + ',' + g2 + ',' + eyg + ',' + X[3].g];
    const cg = X[X.length - 1].g;
    const suf = mg === 'f' ? '眷' : '姻';
    const r = j - 2;
    if (r === 0) return cls + (cg === 'm' ? '兄弟' : '姐妹') + suf;
    if (r === 1) return cls + (cg === 'm' ? '侄' : '侄女') + suf;
    const des = formalDescendant(Array(r - 1).fill('m').concat([cg]));
    return cls + '侄' + des + suf;
  }
  if (n >= 4 && X.slice(0, -1).every(x => x.t === 'P') && (X[X.length - 1].t === 'E' || X[X.length - 1].t === 'Y')) {
    const k = n - 1;
    const eyg = X[X.length - 1].g;
    const mark = { 'm,m': '叔', 'm,f': '姑', 'f,m': '舅', 'f,f': '姨' }[X[X.length - 2].g + ',' + eyg];
    const outer = X[0].g === 'f' ? '外' : '';
    const lv = formalAncestor(Array(k).fill('m')).slice(0, -1);
    return mark + outer + lv + (mg === 'f' ? '眷' : '姻');
  }
  if (n >= 5 && X.slice(0, 3).every(x => x.t === 'P') && (X[3].t === 'E' || X[3].t === 'Y') && X.slice(4).every(x => x.t === 'C')) {
    const pp = X.slice(0, 3);
    const eyg = X[3].g;
    const j = n - 4;
    const cg = X[X.length - 1].g;
    const suf = mg === 'f' ? '眷' : '姻';
    const r = j - 3;
    const mark = { 'm,m': '叔', 'm,f': '姑', 'f,m': '舅', 'f,f': '姨' }[pp[0].g + ',' + cg];
    if (j === 1) {
      const line = {
        'm,m': mg === 'f' ? '从父' : '姑表', 'm,f': mg === 'f' ? '舅表' : '从母',
        'f,m': mg === 'f' ? '从父' : '姑表', 'f,f': mg === 'f' ? '舅表' : '从母'
      }[pp[pp.length - 1].g + ',' + eyg];
      const lv = formalAncestor(Array(-r).fill('m')).slice(0, -1);
      return line + mark + lv + suf;
    }
    let cls;
    if (pp.every(g => g.g === 'm') && eyg === 'm') cls = cousinClass(3, j);
    else {
      const LINE1 = {
        'm,m': mg === 'f' ? '从父' : '姑表', 'm,f': mg === 'f' ? '舅表' : '从母',
        'f,m': mg === 'f' ? '从父' : '姑表', 'f,f': mg === 'f' ? '舅表' : '从母'
      }[pp[pp.length - 1].g + ',' + eyg];
      const LINE2 = { 'm,m': '叔表', 'm,f': '姑表', 'f,m': '舅表', 'f,f': '姨表' };
      cls = LINE1 + LINE2[pp[pp.length - 2].g + ',' + X[4].g];
      for (let d = 2; d < j; d++) cls += LINE2[X[3 + d - 1].g + ',' + X[3 + d].g];
    }
    if (r <= -2) {
      const lv = formalAncestor(Array(-r).fill('m')).slice(0, -1);
      return cls + lv + suf;
    }
    if (r === -1) return cls + mark + suf;
    if (r === 0) return cls + (cg === 'm' ? '兄弟' : '姐妹') + suf;
    if (r === 1) return cls + (cg === 'm' ? '侄' : '侄女') + suf;
    const des = formalDescendant(Array(r - 1).fill('m').concat([cg]));
    return cls + '侄' + des + suf;
  }
  if (n >= 3 && X.every(x => x.t === 'C')) {
    const des = formalDescendant(X.map(x => x.g));
    return des + (mg === 'f' ? '眷' : '姻');
  }
  if (n >= 3 && (X[0].t === 'E' || X[0].t === 'Y') && X.slice(1).every(x => x.t === 'C')) {
    const eyg = X[0].g;
    let des = formalDescendant(X.slice(1).map(x => x.g));
    if (des.endsWith('女')) des = des.slice(0, -1);
    return (eyg === 'm' ? '侄' : '甥') + des + (mg === 'f' ? '眷' : '姻');
  }
  return null;
}

/* 重锚命名 */
function inlawRestName(mateG, s, rest) {
  if (!rest.length) return '';
  if (rest.length >= 2 && rest[rest.length - 1].t === 'M') {
    const raw = inlawRestName(mateG, s, rest.slice(0, -1));
    if (!raw) return '';
    const m2 = rest[rest.length - 1].g;
    const suf = m2 === 'f' ? '妇' : '婿';
    const app = b => {
      if (b.endsWith('女') || b.endsWith('男')) {
        const base = b.slice(0, -1);
        // 只有基词本身带辈分（孙/侄/甥…）时才去掉男/女；
        // 叔/伯/舅/姑/姨 单独不表辈分，保留男/女以免被读成 +1 辈。
        if (/[\u5b59\u4f84\u7525\u5b50\u5973]$/.test(base)) return base + suf;
        return b + suf;
      }
      if (/[\u5144\u5f1f\u59ca\u59b9]$/.test(b)) return b + (m2 === 'f' ? '妇' : '婿');
      if (b.endsWith('父')) return b.slice(0, -1) + (m2 === 'm' ? '父' : '母');
      if (b.endsWith('母')) return b.slice(0, -1) + (m2 === 'm' ? '父' : '母');
      return b + suf;
    };
    if (typeof raw === 'object' && raw !== null) return { primary: app(raw.primary), alts: raw.alts.map(app) };
    return app(raw);
  }
  // 余链中还有配偶（嵌套姻亲）：Y = Y1 + M(g2) + Y2。
  // 先把 Y1 段按段前缀命名，再以 M(g2) 为新锚点递归命名 Y2；
  // 新锚点辈分 s2 = s + priorityOf(Y1)，保证末位呼称的辈分
  // 始终等于目标的绝对辈分（旧实现落到兜底，内层名字整体被当作 Y 的名字）。
  const mi = rest.findIndex(g => g.t === 'M');
  if (mi > 0 && mi < rest.length - 1) {
    const X2 = rest.slice(0, mi), mg2 = rest[mi].g, Y2 = rest.slice(mi + 1);
    const seg2 = inlawSegmentPrefix(X2, mg2);
    if (seg2) {
      const s2 = s + priorityOf(X2);
      const r2 = inlawRestName(mg2, s2, Y2);
      if (r2) {
        if (typeof r2 === 'object' && r2 !== null) {
          return { primary: seg2 + r2.primary, alts: r2.alts.map(a => seg2 + a) };
        }
        return seg2 + r2;
      }
    }
  }
  if (rest.every(g => g.t === 'P')) {
    const gs = rest.map(g => g.g);
    if (s >= 1) return formalAncestor([mateG].concat(Array(s - 1).fill('m'), gs));
    if (s === 0) return formalAncestor(gs);
    const drop = -s;
    if (gs.length <= drop) {
      const gen = s + gs.length;
      if (gen === 0) return gs[gs.length - 1] === 'm' ? '兄弟' : '姊妹';
      if (gen === -1) return gs[gs.length - 1] === 'm' ? '男' : '女';
      return formalDescendantAt(gen, gs[gs.length - 1]);
    }
    return formalAncestor(gs.slice(drop));
  }
  if (rest.length === 1 && (rest[0].t === 'E' || rest[0].t === 'Y')) {
    const ey = rest[0].t, eyg = rest[0].g, gen = s;
    if (gen === 0) return { primary: SIB_F[ey][eyg], alts: [eyg === 'm' ? '兄弟' : '姊妹'] };
    if (gen === 1) {
      if (mateG === 'f') return eyg === 'm' ? '舅父' : '姨母';
      if (eyg === 'm') return { primary: ey === 'E' ? '伯父' : '叔父', alts: ['叔伯父'] };
      return '姑母';
    }
    if (gen === 2) {
      if (mateG === 'f') return eyg === 'm' ? '舅祖父' : '姨祖母';
      return eyg === 'm' ? '叔祖父' : '姑祖母';
    }
    if (gen === -1) return eyg === 'm' ? '男' : '女';
    if (gen === -2) return eyg === 'm' ? '孙男' : '孙女';
    if (gen <= -3) return '曾'.repeat(-gen - 2) + '孙' + (eyg === 'm' ? '男' : '女');
    if (gen >= 3) {
      // 目标在原辈分 gen 上：祖名长度应为 gen（旧实现用 gen-1，
      // 且末字固定为"父"，导致高一辈的目标被降一辈并变成男性）。
      const base = formalAncestor(Array(gen - 1).fill('m').concat([eyg]));
      if (mateG === 'f') return (eyg === 'm' ? '舅' : '姨') + base;
      return (eyg === 'm' ? '叔' : '姑') + base;
    }
    return '';
  }
  if (rest.length >= 2 && rest[0].t === 'P' && rest.slice(0, -1).every(g => g.t === 'P') &&
      (rest[rest.length - 1].t === 'E' || rest[rest.length - 1].t === 'Y')) {
    const pp = rest.slice(0, -1);
    const fg = pp[pp.length - 1].g;
    const ey = rest[rest.length - 1].t, eyg = rest[rest.length - 1].g;
    const gen = s + pp.length;
    if (gen === 0) {
      const flav = eyg === 'm' ? (fg === 'm' ? '叔' : '舅') : (fg === 'm' ? '姑' : '姨');
      return { primary: flav + SIB_F[ey][eyg], alts: [flav + (eyg === 'm' ? '兄弟' : '姊妹')] };
    }
    if (gen === -1) {
      const flav = eyg === 'm' ? (fg === 'm' ? '叔' : '舅') : (fg === 'm' ? '姑' : '姨');
      return flav + (eyg === 'm' ? '男' : '女');
    }
    if (gen <= -2) return formalDescendantAt(gen, eyg);
    if (gen === 1) {
      const t = { 'm,E,m': '伯父', 'm,Y,m': '叔父', 'm,E,f': '姑母', 'm,Y,f': '姑母', 'f,E,m': '舅父', 'f,Y,m': '舅父', 'f,E,f': '姨母', 'f,Y,f': '姨母' };
      return t[fg + ',' + ey + ',' + eyg];
    }
    if (gen === 2) {
      const flav = fg === 'm' ? (eyg === 'm' ? (ey === 'E' ? '伯' : '叔') : '姑') : (eyg === 'm' ? '舅' : '姨');
      const outer = ((s >= 1 && mateG === 'f') || (s === 0 && pp[0].g === 'f')) ? '外' : '';
      return flav + outer + (eyg === 'm' ? '祖父' : '祖母');
    }
    if (gen >= 3) {
      const flav = (ey === 'E' && eyg === 'm' && fg === 'm') ? '伯'
        : (fg === 'm' && eyg === 'm') ? '叔'
        : (fg === 'm') ? '姑'
        : (eyg === 'm') ? '舅' : '姨';
      // 目标在绝对辈分 gen 上：性别序列长度必须为 gen。
      let seq;
      if (s >= 1) seq = [mateG].concat(Array(s - 1).fill('m'), pp.map(g => g.g));
      else seq = pp.map(g => g.g).slice(-gen);
      seq = seq.slice(0, -1).concat([eyg]);
      return flav + formalAncestor(seq);
    }
    return '';
  }
  if ((rest[0].t === 'E' || rest[0].t === 'Y') && rest.slice(1).every(g => g.t === 'C')) {
    const eyg = rest[0].g, cg = rest[rest.length - 1].g;
    const j = rest.length - 1, gen = s - j;
    if (gen === 0) {
      const line = mateG === 'f' ? (eyg === 'm' ? '舅表' : '姨表') : (eyg === 'm' ? '叔表' : '姑表');
      if (cg === 'm') return { primary: line + '兄', alts: [line + '弟', line + '兄弟'] };
      return { primary: line + '姊', alts: [line + '妹', line + '姐妹'] };
    }
    if (gen === 1) {
      if (mateG === 'f') {
        if (cg === 'm') return eyg === 'm' ? '舅表伯父' : '姨表伯父';
        return eyg === 'm' ? '舅表姑母' : '姨表姑母';
      }
      if (cg === 'm') return eyg === 'm' ? '堂伯父' : '堂姑丈';
      return '堂姑母';
    }
    if (s === 0) {
      const stem = eyg === 'm' ? '侄' : '甥';
      if (j === 1) return stem + (cg === 'm' ? '男' : '女');
      return stem + formalDescendant(rest.slice(1).map(g => g.g));
    }
    if (gen === -1) return cg === 'm' ? '男' : '女';
    if (gen <= -2) {
      const seq = [eyg].concat(rest.slice(1).map(g => g.g));
      const des = formalDescendantSeqAt(gen, seq);
      return { primary: des, alts: cg === 'm' ? [des + '男'] : [] };
    }
    if (gen >= 2) {
      const line = eyg === 'm' ? (mateG === 'f' ? '舅表' : '叔表') : (mateG === 'f' ? '姨表' : '姑表');
      const lv = formalAncestor(Array(gen).fill('m')).slice(0, -1);
      if (cg === 'm') return { primary: line + '伯叔' + lv + '父', alts: [line + '伯' + lv + '父', line + '叔' + lv + '父'] };
      return line + '姑' + lv + '母';
    }
    return '';
  }
  if (rest.length >= 3 && rest[0].t === 'P' && (rest[1].t === 'E' || rest[1].t === 'Y') &&
      rest.slice(2).every(g => g.t === 'C')) {
    const fg = rest[0].g, eyg = rest[1].g, cg = rest[rest.length - 1].g;
    const gen = s + 1 - (rest.length - 2);
    if (gen === 0) {
      const line = { 'm,m': '叔表', 'm,f': '姑表', 'f,m': '舅表', 'f,f': '姨' }[fg + ',' + eyg];
      if (cg === 'm') return { primary: line + '兄', alts: [line + '弟', line + '兄弟'] };
      return { primary: line + '姊', alts: [line + '妹', line + '姐妹'] };
    }
    if (gen === -1) {
      const flav = eyg === 'm' ? (fg === 'm' ? '叔' : '舅') : (fg === 'm' ? '姑' : '姨');
      return flav + (cg === 'm' ? '男' : '女');
    }
    if (gen <= -2) {
      const seq = [eyg].concat(rest.slice(2).map(g => g.g));
      return formalDescendantSeqAt(gen, seq);
    }
    if (gen === 1) {
      if (mateG === 'f') return cg === 'm' ? '堂舅父' : '堂姨母';
      if (cg === 'm') return '堂伯父';
      return '堂姑母';
    }
    if (gen >= 2) {
      const line = { 'm,m': '叔表', 'm,f': '姑表', 'f,m': '舅表', 'f,f': '姨表' }[fg + ',' + eyg];
      const lv = formalAncestor(Array(gen).fill('m')).slice(0, -1);
      if (cg === 'm') return { primary: line + '伯叔' + lv + '父', alts: [line + '伯' + lv + '父', line + '叔' + lv + '父'] };
      return line + '姑' + lv + '母';
    }
    return '';
  }
  return '';
}

function priorityOf(gens) {
  let p = 0;
  for (const g of gens) {
    if (g.t === 'P') p += 1;
    else if (g.t === 'C') p -= 1;
  }
  return p;
}

function nameMateFirst(mg, rest) {
  if (!rest.length) return { primary: SPOUSE[mg], alts: SPOUSE_ALTS[mg] };
  if (rest.every(g => g.t === 'P')) {
    const gs = rest.map(g => g.g);
    if (gs.length === 1) return { primary: MATE_PARENT[mg + ',' + gs[0]], alts: [] };
    if (gs.length === 2) {
      const base = formalAncestor(gs);
      return { primary: mateAncestorInsert(base, mg), alts: [(mg === 'f' ? '妻' : '夫') + base] };
    }
    const base = nameAncestors(gs).primary;
    return { primary: mateAncestorInsert(base, mg), alts: [(mg === 'f' ? '妻' : '夫') + base] };
  }
  if (rest.length === 1 && (rest[0].t === 'E' || rest[0].t === 'Y')) {
    const ey = rest[0].t, eyg = rest[0].g;
    return { primary: MATE_SIB[mg + ',' + ey + ',' + eyg], alts: MATE_SIB_GEN[mg + ',' + eyg] || [] };
  }
  if (rest.length === 2 && (rest[0].t === 'E' || rest[0].t === 'Y') && rest[1].t === 'M') {
    return mateSibMateNames(mg, rest[0].t, rest[0].g, rest[1].g);
  }
  if (rest.length >= 3 && (rest[0].t === 'E' || rest[0].t === 'Y') &&
      rest.slice(1, -1).every(g => g.t === 'C') && rest[rest.length - 1].t === 'M') {
    const eyg = rest[0].g;
    const cgs = rest.slice(1, -1).map(g => g.g);
    const m2 = rest[rest.length - 1].g;
    const core = MATE_NEPHEW[mg + ',' + eyg + ',' + cgs[cgs.length - 1]][0];
    const stem = core.endsWith('女') ? core.slice(0, -1) : core;
    const base = cgs.length === 1 ? core : stem + formalDescendant(cgs);
    if (base.endsWith('女')) {
      return m2 === 'm' ? { primary: base + '婿', alts: [] } : { primary: base + '媳', alts: [] };
    }
    if (cgs.length >= 2) return { primary: base + (m2 === 'f' ? '妇' : '婿'), alts: [] };
    return { primary: base + (m2 === 'f' ? '媳妇' : '婿'), alts: [] };
  }
  if (rest.length >= 3 && (rest[0].t === 'E' || rest[0].t === 'Y') && rest[1].t === 'M') {
    const seg = inlawSegmentPrefix([{ t: 'M', g: mg }, rest[0]], rest[1].g);
    if (seg) {
      const rn = inlawRestName(rest[1].g, 0, rest.slice(2));
      if (rn) return (typeof rn === 'object' && rn !== null) ? { primary: seg + rn.primary, alts: rn.alts.map(a => seg + a) } : { primary: seg + rn, alts: [] };
    }
  }
  if (rest.length >= 3 && (rest[0].t === 'E' || rest[0].t === 'Y') && rest[1].t === 'C') {
    const ti = rest.findIndex((g, i) => i >= 2 && g.t === 'M');
    if (ti >= 0) {
      const eyg = rest[0].g;
      const cgs = rest.slice(1, ti).map(g => g.g);
      const core = MATE_NEPHEW[mg + ',' + eyg + ',' + cgs[cgs.length - 1]][0];
      const stem = core.endsWith('女') ? core.slice(0, -1) : core;
      const prefix = cgs.length === 1 ? stem : stem + formalDescendant(cgs);
      const s2 = cgs.length === 1 ? -1 : -cgs.length;
      const m2 = rest[ti].g;
      const rn = inlawRestName(m2, s2, rest.slice(ti + 1));
      if (rn) {
        const base = prefix + (m2 === 'f' ? '眷' : '姻');
        return (typeof rn === 'object' && rn !== null) ? { primary: base + rn.primary, alts: rn.alts.map(a => base + a) } : { primary: base + rn, alts: [] };
      }
    }
  }
  if ((rest[0].t === 'E' || rest[0].t === 'Y') && rest.slice(1).every(g => g.t === 'C')) {
    const eyg = rest[0].g, j = rest.length - 1;
    const core = MATE_NEPHEW[mg + ',' + eyg + ',' + rest[rest.length - 1].g];
    if (j === 1) return { primary: core[0], alts: core[1] };
    const stem = core[0].endsWith('女') ? core[0].slice(0, -1) : core[0];
    return { primary: stem + formalDescendant(rest.slice(1).map(g => g.g)), alts: core[1] };
  }
  if (rest[0].t === 'P') {
    let k = 1;
    while (k < rest.length && rest[k].t === 'P') k++;
    if (k < rest.length && (rest[k].t === 'E' || rest[k].t === 'Y')) {
      const ey = rest[k].t, eyg = rest[k].g, tail = rest.slice(k + 1);
      if (!tail.length) {
        if (k === 1) return { primary: MATE_UNCLE1[mg + ',' + rest[0].g + ',' + ey + ',' + eyg], alts: [] };
        const line = mateUncleLine(rest.slice(0, k), ey, eyg);
        let base = mateAncestorInsert(formalAncestor(rest.slice(0, k).map(g => g.g)), mg);
        if (/[\u516c\u5a46][\u7236\u6bcd]$/.test(base)) base = base.slice(0, -2) + (eyg === 'm' ? '公父' : '婆母');
        else base = base.slice(0, -1) + (eyg === 'm' ? '父' : '母');
        const uprim = nameUncle(rest.slice(0, k), ey, eyg);
        const other = mg === 'f' ? '妻' : '夫';
        return {
          primary: line + base,
          alts: [(mg === 'f' ? '岳' : '公') + uprim.primary, other + uprim.primary].concat(uprim.alts.map(a => other + a))
        };
      }
      if (tail.every(g => g.t === 'C')) {
        if (k === 1 && tail.length === 1) {
          const line = { 'm,m': '堂', 'm,f': '姑表', 'f,m': '舅表', 'f,f': '姨' }[rest[0].g + ',' + eyg];
          const cg = tail[0].g;
          const stem = mg === 'f' ? (cg === 'm' ? '舅子' : '姨子') : (cg === 'm' ? '伯子' : '姑子');
          const altStem = mg === 'f' ? stem : (cg === 'm' ? '叔子' : stem);
          return { primary: line + '大' + stem, alts: [line + '小' + altStem] };
        }
        if (k === 2 && tail.length === 1) {
          if (mg === 'f' && rest[0].g === 'm' && rest[1].g === 'm' && eyg === 'm') {
            if (tail[0].g === 'm') return { primary: '姻伯丈', alts: ['姻叔丈'] };
            return { primary: '堂姑岳母', alts: [] };
          }
          const line1 = { 'm,m': '堂', 'm,f': '姑表', 'f,m': '舅表', 'f,f': '姨' }[rest[1].g + ',' + eyg];
          if (rest[0].g === 'm') {
            if (tail[0].g === 'm') {
              const suf = mg === 'f' ? '岳父' : '公父';
              return { primary: line1 + '伯' + suf, alts: [line1 + '叔' + suf] };
            }
            const suf = mg === 'f' ? '岳母' : '婆母';
            return { primary: line1 + '姑' + suf, alts: [] };
          }
          if (tail[0].g === 'm') {
            const suf = mg === 'f' ? '岳父' : '公父';
            return { primary: line1 + '舅' + suf, alts: [] };
          }
          const suf = mg === 'f' ? '岳母' : '婆母';
          return { primary: line1 + '姨' + suf, alts: [] };
        }
        // 其余（k>=1 且 j>=2，或 k>=3 且 j==1）：配偶视角完整命名
        const res = nameCousinLine(rest.slice(0, k), ey, eyg, tail);
        if (k > tail.length) {          // r = j-k < 0：岳/公父/婆母 终端插入
          const ins = mateAncestorInsert(res.primary, mg);
          const insAlts = [];
          for (const a of res.alts) {
            const ia = mateAncestorInsert(a, mg);
            if (ia !== a && !insAlts.includes(ia)) insAlts.push(ia);
          }
          return { primary: ins, alts: insAlts };
        }
        const pref = mg === 'm' ? '夫' : '妻';
        return { primary: pref + res.primary, alts: res.alts.map(a => pref + a) };
      }
      if (k === 1 && tail.length === 2 && tail[0].t === 'C' && tail[1].t === 'M') {
        const line = { 'm,m': '堂', 'm,f': '姑表', 'f,m': '舅表', 'f,f': '姨' }[rest[0].g + ',' + eyg];
        const res = mateSibMateNames(mg, 'E', tail[0].g, tail[1].g);
        return { primary: line + res.primary, alts: res.alts.map(a => line + a) };
      }
      if (k >= 2 && tail.length === 1 && tail[0].t === 'M') {
        const line = mateUncleLine(rest.slice(0, k), ey, eyg);
        const m2 = tail[0].g;
        let base = mateAncestorInsert(formalAncestor(rest.slice(0, k).map(g => g.g)), mg);
        if (/[\u516c\u5a46][\u7236\u6bcd]$/.test(base)) base = base.slice(0, -2) + (m2 === 'm' ? '公父' : '婆母');
        else base = base.slice(0, -1) + (m2 === 'm' ? '父' : '母');
        if (m2 === eyg) return { primary: line + base + (m2 === 'm' ? '婿' : '媳'), alts: [] };
        return { primary: line + base, alts: [] };
      }
      if (tail.some(g => g.t === 'M')) {
        const ti = tail.findIndex(g => g.t === 'M');
        const seg = inlawSegmentPrefix(rest.slice(0, k).concat([rest[k]]).concat(tail.slice(0, ti)), tail[ti].g);
        if (seg) {
          const s = priorityOf(rest.slice(0, k).concat([rest[k]]).concat(tail.slice(0, ti)));
          const rn = inlawRestName(tail[ti].g, s, tail.slice(ti + 1));
          if (rn) {
            const pref = mg === 'm' ? '夫' : '妻';
            return (typeof rn === 'object' && rn !== null)
              ? { primary: pref + seg + rn.primary, alts: rn.alts.map(a => pref + seg + a) }
              : { primary: pref + seg + rn, alts: [] };
          }
        }
        // 重锚失败且 tail 不是“纯 C 链 + 末位 M”时，nameCousinMate 无法处理。
        if (!(tail.slice(0, -1).every(g => g.t === 'C') && tail[tail.length - 1].t === 'M')) {
          const tg = priorityOf(rest);
          return { primary: (mg === 'f' ? '妻' : '夫') + termAtGeneration(tg, rest[rest.length - 1].g), alts: [] };
        }
      }
      const res = nameCousinMate(rest.slice(0, k), ey, eyg, tail.slice(0, -1), tail[tail.length - 1].g);
      if (k > tail.length - 1) {       // r < 0：岳/公父/婆母 终端插入
        return { primary: mateAncestorInsert(res.primary, mg), alts: [] };
      }
      return { primary: (mg === 'm' ? '夫' : '妻') + res.primary, alts: [] };
    }
  }
  const tg = priorityOf(rest);
  return { primary: (mg === 'f' ? '妻' : '夫') + termAtGeneration(tg, rest[rest.length - 1].g), alts: [] };
}

function nameMateLast(mg, X) {
  const n = X.length;
  if (n === 0) return { primary: SPOUSE[mg], alts: SPOUSE_ALTS[mg] };
  if (n === 1 && (X[0].t === 'E' || X[0].t === 'Y')) return nameSiblingMate(X[0].t, X[0].g, mg);
  if (X.every(g => g.t === 'C')) {
    if (n === 1) {
      if (X[0].g === 'm') return mg === 'f' ? { primary: '儿媳', alts: [] } : { primary: '儿婿', alts: [] };
      return mg === 'm' ? { primary: '女婿', alts: [] } : { primary: '女媳', alts: [] };
    }
    const base = formalDescendant(X.map(g => g.g));
    if (n === 2) {
      if (base.endsWith('女')) return mg === 'm' ? { primary: base + '婿', alts: [] } : { primary: base + '媳', alts: [] };
      return mg === 'f' ? { primary: base + '媳妇', alts: [] } : { primary: base + '婿', alts: [] };
    }
    if (base.endsWith('女')) return mg === 'm' ? { primary: base + '婿', alts: [] } : { primary: base + '媳', alts: [] };
    return mg === 'f' ? { primary: base + '媳妇', alts: [base + '妇'] } : { primary: base + '婿', alts: [] };
  }
  if (n === 2 && X[0].t === 'M' && (X[1].t === 'E' || X[1].t === 'Y')) {
    return mateSibMateNames(X[0].g, X[1].t, X[1].g, mg);
  }
  if (n >= 2 && X[0].t === 'M') {
    const inner = X.slice(1);
    if (inner.length >= 2 && (inner[0].t === 'E' || inner[0].t === 'Y') && inner.slice(1).every(g => g.t === 'C')) {
      const eyg = inner[0].g;
      const cgs = inner.slice(1).map(g => g.g);
      const core = MATE_NEPHEW[X[0].g + ',' + eyg + ',' + cgs[cgs.length - 1]][0];
      const stem = core.endsWith('女') ? core.slice(0, -1) : core;
      if (cgs.length === 1) {
        const base = core;
        if (base.endsWith('女')) return mg === 'm' ? { primary: base + '婿', alts: [] } : { primary: base + '媳', alts: [] };
        return mg === 'f' ? { primary: base + '媳妇', alts: [] } : { primary: base + '婿', alts: [] };
      }
      const base = stem + formalDescendant(cgs);
      if (base.endsWith('女')) return mg === 'm' ? { primary: base.slice(0, -1) + '婿', alts: [] } : { primary: base + '媳', alts: [] };
      return { primary: base + (mg === 'f' ? '妇' : '婿'), alts: [] };
    }
    let k = 1;
    while (k < inner.length && inner[k].t === 'P') k++;
    if (k >= 1 && k < inner.length && (inner[k].t === 'E' || inner[k].t === 'Y') &&
        inner.slice(0, k).every(g => g.t === 'P')) {
      const ey = inner[k].t, eyg = inner[k].g, tail = inner.slice(k + 1);
      if (!tail.length) {
        const line = mateUncleLine(inner.slice(0, k), ey, eyg);
        let base;
        if (k === 1) {
          base = { 'f,m': '岳父', 'f,f': '岳母', 'm,m': '公父', 'm,f': '婆母' }[X[0].g + ',' + mg];
          if (mg === eyg) return { primary: line + base + (mg === 'm' ? '婿' : '媳'), alts: [] };
        } else {
          base = mateAncestorInsert(formalAncestor(inner.slice(0, k).map(g => g.g)), X[0].g);
          if (/[\u516c\u5a46][\u7236\u6bcd]$/.test(base)) base = base.slice(0, -2) + (mg === 'm' ? '公父' : '婆母');
          else base = base.slice(0, -1) + (mg === 'm' ? '父' : '母');
          if (mg === eyg) return { primary: line + base + (mg === 'm' ? '婿' : '媳'), alts: [] };
        }
        return { primary: line + base, alts: [] };
      }
      if (tail.length === 1 && tail[0].t === 'C') {
        if (k === 1) {
          // 配偶堂表兄弟姐妹的配偶（库词形）：堂大姑夫/堂大婶子/堂大舅嫂…
          const line = { 'm,m': '堂', 'm,f': '姑表', 'f,m': '舅表', 'f,f': '姨' }[inner[0].g + ',' + eyg];
          const res = mateSibMateNames(X[0].g, 'E', tail[0].g, mg);
          return { primary: line + res.primary, alts: res.alts.map(a => line + a) };
        }
        // k>=2：配偶之高辈表亲的配偶（r<0 做终端插入，否则 夫/妻 + 配偶视角）
        const res = nameCousinMate(inner.slice(0, k), ey, eyg, tail, mg);
        if (k > tail.length) {
          return { primary: mateAncestorInsert(res.primary, X[0].g), alts: [] };
        }
        const pref = X[0].g === 'm' ? '夫' : '妻';
        return { primary: pref + res.primary, alts: res.alts.map(a => pref + a) };
      }
    }
  }
  if (X[0].t === 'P') {
    let k = 1;
    while (k < n && X[k].t === 'P') k++;
    if (k < n && (X[k].t === 'E' || X[k].t === 'Y')) {
      const ey = X[k].t, eyg = X[k].g, tail = X.slice(k + 1);
      if (!tail.length) {
        const pp = X.slice(0, k);
        if (k === 1) {
          const t = UNCLE1_MATE[pp[0].g + ',' + ey + ',' + eyg][mg];
          return { primary: t[0], alts: t[1] };
        }
        if (k === 2) {
          const key = pp[0].g + ',' + pp[1].g + ',' + ey + ',' + eyg;
          if (UNCLE2_MATE[key] && UNCLE2_MATE[key][mg]) {
            const alts = (pp[0].g + ',' + pp[1].g + ',' + eyg) === 'm,f,m' ? ['舅奶奶'] : [];
            return { primary: UNCLE2_MATE[key][mg], alts };
          }
          const un = nameUncle(pp, ey, eyg).primary;
          return { primary: un + (mg === 'm' ? '婿' : '媳'), alts: [] };
        }
        const anc = formalAncestor(pp.map(g => g.g)).slice(0, -1) + (mg === 'm' ? '父' : '母');
        const line = mateUncleLine(pp, ey, eyg);
        const ualts = nameUncle(pp, ey, eyg).alts;
        if (mg === eyg) return { primary: line + anc + (mg === 'm' ? '婿' : '媳'), alts: [] };
        return { primary: line + anc, alts: ualts.map(a => a.slice(0, -1) + (mg === 'm' ? '父' : '母')) };
      }
      if (tail.every(g => g.t === 'C')) return nameCousinMate(X.slice(0, k), ey, eyg, tail, mg);
    }
  }
  if (n >= 1 && (X[0].t === 'E' || X[0].t === 'Y') && X.slice(1).every(g => g.t === 'C')) {
    return nameNephewMate(X[0].t, X[0].g, X.slice(1), mg);
  }
  if (n === 3 && X[0].t === 'C' && X[1].t === 'M' && (X[2].t === 'E' || X[2].t === 'Y')) {
    return mg === 'f' ? { primary: '姻侄媳', alts: [] } : { primary: '姻侄婿', alts: [] };
  }
  // 段前缀 + 重锚：X 内含 Mate（不限 X 的首段类型）
  // 例：父之母之姐之妻之兄 + 妻 → 段前缀“姨祖眷” + 重锚“舅祖母”
  if (n >= 2 && X.some(g => g.t === 'M')) {
    const ti = X.findIndex(g => g.t === 'M');
    if (ti > 0 && ti < n - 1) {
      const seg = inlawSegmentPrefix(X.slice(0, ti), X[ti].g);
      if (seg) {
        const s = priorityOf(X.slice(0, ti));
        const rn = inlawRestName(X[ti].g, s, X.slice(ti + 1).concat([{ t: 'M', g: mg }]));
        if (rn) return (typeof rn === 'object' && rn !== null) ? { primary: seg + rn.primary, alts: rn.alts.map(a => seg + a) } : { primary: seg + rn, alts: [] };
      }
    }
  }
  const res = nameKm(X);
  const prim = res.primary, alts = res.alts;
  if (/[\u5144\u5f1f\u59d0\u59b9\u59ca]$/.test(prim)) {
    return { primary: prim + (mg === 'f' ? '妇' : '婿'), alts: alts.filter(a => a !== prim).map(a => a + (mg === 'f' ? '妇' : '婿')) };
  }
  // 口语兄弟姐妹词 + 配偶：用“嫂子/弟媳/姐夫/妹夫”等替换，而不是“哥哥媳妇/姐姐婿”。
  const COLLOQUIAL_SIB = { '哥哥': ['E', 'm'], '姐姐': ['E', 'f'], '弟弟': ['Y', 'm'], '妹妹': ['Y', 'f'] };
  for (const sib of Object.keys(COLLOQUIAL_SIB)) {
    if (prim.endsWith(sib)) {
      const ey = COLLOQUIAL_SIB[sib][0], eyg = COLLOQUIAL_SIB[sib][1];
      const smRes = nameSiblingMate(ey, eyg, mg);
      const stem = prim.slice(0, -sib.length);
      const out = smRes.alts.map(a => stem + a);
      for (const a of alts) {
        if (a === prim) continue;
        out.push(a.endsWith(sib) ? stem + smRes.primary : a + (mg === 'f' ? '妇' : '婿'));
      }
      return { primary: stem + smRes.primary, alts: [...new Set(out)] };
    }
  }
  if (prim.endsWith('父')) {
    const sw = a => a.slice(0, -1) + (mg === 'm' ? '父' : '母');
    return { primary: sw(prim), alts: alts.filter(a => a !== prim).map(sw) };
  }
  if (prim.endsWith('母')) {
    const sw = a => a.slice(0, -1) + (mg === 'm' ? '父' : '母');
    return { primary: sw(prim), alts: alts.filter(a => a !== prim).map(sw) };
  }
  if (/^(\u53d4\u4f84|\u8205\u4f84|\u59d1\u7525|\u59e8\u7525)/.test(prim) && prim.endsWith('女')) {
    return mg === 'm' ? { primary: prim + '婿', alts: [] } : { primary: prim + '媳', alts: [] };
  }
  if (prim.endsWith('男')) {
    const base = prim.slice(0, -1);
    // 只有“孙/侄/甥…”这类本身带辈分的词才能省掉“男”。
    const stem = /[\u5b59\u4f84\u7525\u5b50\u5973]$/.test(base) ? base : prim;
    return { primary: stem + (mg === 'f' ? '妇' : '婿'), alts: [] };
  }
  if (prim.endsWith('女')) {
    const base = prim.slice(0, -1);
    const stem = /[\u5b59\u4f84\u7525\u5b50\u5973]$/.test(base) ? base : prim;
    return { primary: stem + (mg === 'm' ? '婿' : '媳'), alts: [] };
  }
  if (X[X.length - 1].g === 'm') {
    return mg === 'f' ? { primary: prim + '媳妇', alts: [] } : { primary: prim + '婿', alts: [] };
  }
  return mg === 'm' ? { primary: prim + '婿', alts: [] } : { primary: prim + '媳', alts: [] };
}

function nameMateMiddle(gens, i, mg) {
  const X = gens.slice(0, i), Y = gens.slice(i + 1);
  if (X.length === 1 && X[0].t === 'C' && Y.length === 1 && Y[0].t === 'P') {
    return { primary: Y[0].g === 'm' ? '亲家公' : '亲家母', alts: [] };
  }
  if (X.length === 1 && X[0].t === 'C' && Y.length && (Y[0].t === 'E' || Y[0].t === 'Y') &&
      Y.slice(1).every(g => g.t === 'C')) {
    if (Y.length === 1) return { primary: Y[0].g === 'm' ? '姻侄' : '姻侄女', alts: [] };
    const des = formalDescendant([Y[0].g].concat(Y.slice(1).map(g => g.g)));
    return { primary: '姻侄' + des, alts: [] };
  }
  if (X.length === 1 && X[0].t === 'C' && Y.length === 2 && (Y[0].t === 'E' || Y[0].t === 'Y') && Y[1].t === 'M') {
    return Y[1].g === 'f' ? { primary: '姻侄媳', alts: [] } : { primary: '姻侄婿', alts: [] };
  }
  const s = priorityOf(X);
  const seg = inlawSegmentPrefix(X, mg);
  const rn = inlawRestName(mg, s, Y);
  if (seg && rn) {
    if (typeof rn === 'object' && rn !== null) {
      return { primary: seg + rn.primary, alts: rn.alts.map(a => seg + a) };
    }
    return { primary: seg + rn, alts: [] };
  }
  const px = nameMateLast(mg, X);
  let stem = px.primary;
  const sufs = ['媳妇', '女婿', '之夫', '之妻', '妻', '夫', '妇', '媳', '婿', '嫂'];
  for (const sf of sufs) {
    if (stem.endsWith(sf)) { stem = stem.slice(0, -sf.length); break; }
  }
  const prefix = stem + (mg === 'f' ? '眷' : '姻');
  // 优先用重锚名（已经是目标的绝对辈分）
  if (rn) {
    if (typeof rn === 'object' && rn !== null) {
      return { primary: prefix + rn.primary, alts: rn.alts.map(a => prefix + a) };
    }
    return { primary: prefix + rn, alts: [] };
  }
  // 最后兜底：按 s + Y 的辈分取通用词，保证辈分/性别不再错位
  const tg = s + priorityOf(Y);
  return { primary: prefix + termAtGeneration(tg, Y[Y.length - 1].g), alts: [] };
}

function nameKm(gens) {
  if (!gens || !gens.length) return { primary: '自己', alts: [] };
  if (gens.length === 1) {
    const g = gens[0];
    if (g.t === 'I') return { primary: '自己', alts: [] };
    if (g.t === 'Z') return { primary: '无', alts: [] };
    if (g.t === 'P') return { primary: PARENT[g.g], alts: PARENT_ALTS[g.g] };
    if (g.t === 'C') return { primary: CHILD[g.g], alts: CHILD_ALTS[g.g] };
    if (g.t === 'M') return { primary: SPOUSE[g.g], alts: SPOUSE_ALTS[g.g] };
    const ey = g.t;
    return { primary: SIB[ey][g.g], alts: SIB_ALTS[ey][g.g] };
  }
  if (gens.every(g => g.t === 'P')) return nameAncestors(gens.map(g => g.g));
  if (gens.every(g => g.t === 'C')) return nameDescendants(gens.map(g => g.g));
  const mpos = gens.map((g, i) => (g.t === 'M' ? i : -1)).filter(i => i >= 0);
  if (mpos.length) {
    if (mpos[mpos.length - 1] === gens.length - 1) return nameMateLast(gens[gens.length - 1].g, gens.slice(0, -1));
    if (mpos[0] === 0) return nameMateFirst(gens[0].g, gens.slice(1));
    return nameMateMiddle(gens, mpos[0], gens[mpos[0]].g);
  }
  if (gens[0].t === 'E' || gens[0].t === 'Y') return nameSiblingLine(gens[0].t, gens[0].g, gens.slice(1));
  let k = 0;
  while (k < gens.length && gens[k].t === 'P') k++;
  const eyGen = gens[k], ey = eyGen.t, rest = gens.slice(k + 1);
  if (!rest.length) return nameUncle(gens.slice(0, k), ey, eyGen.g);
  return nameCousinLine(gens.slice(0, k), ey, eyGen.g, rest);
}

/* ------------------------------ 顶层入口 ------------------------------ */

const CHAIN_HAN = {
  P: { m: '父', f: '母' }, C: { m: '子', f: '女' }, M: { m: '夫', f: '妻' },
  E: { m: '兄', f: '姐' }, Y: { m: '弟', f: '妹' }
};

function chainToText(gens) {
  return gens.map(g => {
    if (g.t === 'I') return '己';
    if (g.t === 'Z') return '0';
    return CHAIN_HAN[g.t][g.g];
  }).join('的');
}

// 备选名去重，并去掉与主名相同的项（否则页面会出现"堂姑（亦作：堂姑）"）
function cleanAlternatives(primary, alts) {
  const out = [];
  for (const a of alts || []) {
    if (a && a !== primary && !out.includes(a)) out.push(a);
  }
  return out;
}

function nameChain(gens, egoG) {
  const notes = [];
  for (let i = 0; i < gens.length - 1; i++) {
    const a = gens[i], b = gens[i + 1];
    if (a.t === 'P' && b.t === 'M') {
      if (a.g === b.g) {
        notes.push('同性婚姻：' + (a.g === 'f' ? '母' : '父') + '之' + (b.g === 'f' ? '妻' : '夫') +
          '（两位' + (a.g === 'f' ? '妈妈' : '爸爸') + '，与生身父母同称）');
      } else {
        notes.push((a.g === 'f' ? '母' : '父') + '之' + (b.g === 'f' ? '妻' : '夫') + '即' +
          (b.g === 'f' ? '妈妈' : '爸爸') + '（若非生身父母亦可称继' + (b.g === 'f' ? '母' : '父') + '）');
      }
    } else if (a.t === 'M' && b.t === 'C') {
      notes.push((a.g === 'f' ? '妻' : '夫') + '之' + (b.g === 'f' ? '女' : '子') + '即亲生' +
        (b.g === 'f' ? '女儿' : '儿子') + '（若非亲生亦可称继' + (b.g === 'f' ? '女' : '子') + '）');
    } else if (a.t === 'M' && b.t === 'M') {
      notes.push('配偶之配偶即自己');
    }
  }
  const red = init(gens);
  // "我"的性别已知时，化简结果里形如 I(g) 的"自己"分支只有在 g 与"我"一致时才成立。
  // 例如"爸爸的女儿"在"我"为男时只能是姐姐/妹妹，不能是自己。
  let monos = red.monomials;
  if (egoG === 'm' || egoG === 'f') {
    monos = monos.filter(m => !(m.length === 1 && m[0].t === 'I' && m[0].g != null && m[0].g !== egoG));
    if (!monos.length) monos = [[{ t: 'Z', g: null }]];
  }
  const entries = [];
  const seen = {};
  for (const mono of monos) {
    if (mono.length === 1 && mono[0].t === 'Z') continue;
    const res = nameKm(mono);
    const key = res.primary;
    if (seen[key]) continue;
    seen[key] = true;
    entries.push({ monomial: mono.map(x => x.t + (x.g || '')).join(''), primary: res.primary, alternatives: cleanAlternatives(res.primary, res.alts) });
  }
  if (!entries.length) {
    notes.length = 0;
    notes.push('关系链化简为 0：链路内的性别相互矛盾，此关系不成立。');
  }
  return {
    chain: chainToText(gens),
    formula: monos.map(m => m.map(x => x.t + (x.g || '')).join('')).join(' + '),
    entries,
    primary: entries.length ? entries.map(e => e.primary).join(' / ') : '无（此关系不成立）',
    notes
  };
}

/* ------------------------------ 关系转换（A→B） ------------------------------ */

// 链的逆：gens 为"我→某人"的生成元链；返回"某人→我"的链。
// 每个生成元取反（P↔C、E↔Y、M 不变），性别取"被描述者"的性别；
// 第一个（离"某人"最近的）逆生成元描述的是"我"，其性别 = egoG。
function invertChain(gens, egoG) {
  const inv = [];
  for (let i = gens.length - 1; i >= 0; i--) {
    const g = gens[i];
    let t = g.t;
    if (t === 'P') t = 'C';
    else if (t === 'C') t = 'P';
    else if (t === 'E') t = 'Y';
    else if (t === 'Y') t = 'E';
    const prevG = i === 0 ? egoG : gens[i - 1].g;
    inv.push({ t, g: prevG });
  }
  return inv;
}

function _scanNotes(full) {
  const notes = [];
  for (let i = 0; i < full.length - 1; i++) {
    const a = full[i], b = full[i + 1];
    if (a.t === 'P' && b.t === 'M') {
      if (a.g === b.g) {
        notes.push('同性婚姻：' + (a.g === 'f' ? '母' : '父') + '之' + (b.g === 'f' ? '妻' : '夫') +
          '（两位' + (a.g === 'f' ? '妈妈' : '爸爸') + '，与生身父母同称）');
      } else {
        notes.push((a.g === 'f' ? '母' : '父') + '之' + (b.g === 'f' ? '妻' : '夫') + '即' +
          (b.g === 'f' ? '妈妈' : '爸爸') + '（若非生身父母亦可称继' + (b.g === 'f' ? '母' : '父') + '）');
      }
    } else if (a.t === 'M' && b.t === 'C') {
      notes.push((a.g === 'f' ? '妻' : '夫') + '之' + (b.g === 'f' ? '女' : '子') + '即亲生' +
        (b.g === 'f' ? '女儿' : '儿子') + '（若非亲生亦可称继' + (b.g === 'f' ? '女' : '子') + '）');
    } else if (a.t === 'M' && b.t === 'M') {
      notes.push('配偶之配偶即自己');
    }
  }
  return notes;
}

// A→B 呼称：chainA/chainB 为"我→A / 我→B"的链；egoG 为"我"的性别（必须 m/f）；
// genderA 为 A 的性别（A 链末位生成元的性别，A=我时即 egoG）。
function relateNames(chainA, chainB, egoG, genderA) {
  const full = invertChain(chainA, egoG).concat(chainB);
  const red = init(full);
  const entries = [];
  const seen = {};
  for (const mono of red.monomials) {
    if (mono.length === 1 && mono[0].t === 'Z') continue;
    // "B 即 A 本人"（I 分支）只有在我=A 且性别一致时才可能成立
    if (mono.length === 1 && mono[0].t === 'I' && mono[0].g && genderA && mono[0].g !== genderA) continue;
    const res = nameKm(mono);
    if (seen[res.primary]) continue;
    seen[res.primary] = true;
    entries.push({ monomial: mono.map(x => x.t + (x.g || '')).join(''), primary: res.primary, alternatives: cleanAlternatives(res.primary, res.alts) });
  }
  const notes = _scanNotes(full);
  if (!entries.length) {
    notes.length = 0;
    notes.push('关系链化简为 0：链路内的性别相互矛盾，此关系不成立。');
  }
  return {
    chain: chainToText(full),
    formula: red.monomials.map(m => m.map(x => x.t + (x.g || '')).join('')).join(' + '),
    entries,
    primary: entries.length ? entries.map(e => e.primary).join(' / ') : '无（此关系不成立）',
    notes
  };
}

// 顶层便捷入口：egoG 未设置（null）时，分别按"我"为男/女计算并合并结果。
function relate(chainA, chainB, egoG, genderA) {
  if (egoG === 'm' || egoG === 'f') return relateNames(chainA, chainB, egoG, genderA);
  const rM = relateNames(chainA, chainB, 'm', genderA);
  const rF = relateNames(chainA, chainB, 'f', genderA);
  const entries = [];
  const seen = {};
  const notes = [];
  for (const e of rM.entries.concat(rF.entries)) {
    if (seen[e.primary]) continue;
    seen[e.primary] = true;
    entries.push(e);
  }
  for (const n of rM.notes.concat(rF.notes)) {
    if (notes.includes(n)) continue;
    // 一种性别下"不成立"，另一种性别下有结果时，不该把失败提示也带上
    if (entries.length && n.indexOf('关系链化简为 0') === 0) continue;
    notes.push(n);
  }
  return {
    chain: rM.chain,
    formula: rM.formula,
    entries,
    primary: entries.length ? entries.map(e => e.primary).join(' / ') : '无（此关系不成立）',
    notes,
    ambiguous: rM.primary !== rF.primary
  };
}

/* Node 环境导出 */
if (typeof module !== 'undefined' && module.exports) {
  module.exports = {
    init, nameKm, nameChain, nameAncestors, nameDescendants, formalAncestor, formalDescendant,
    invertChain, relateNames, relate
  };
}
