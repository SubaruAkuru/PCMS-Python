<p align="center">
  <img src="docs/cover.png" width="300" alt="《亲属关系的代数与命名》封面">
</p>

<h1 align="center">PCMS-Kin</h1>

<p align="center">
  <b>亲属关系的代数与命名</b><br>
  <b>The Algebra and Grammar of Kinship</b>
</p>

<p align="center">
  用关系代数、十三条公理与形式语法，生成任意深度的中文亲属称呼。<br>
  An axiom-based kinship algebra and Chinese kinship-term generator.
</p>

<p align="center">
  <a href="#中文">中文</a> ·
  <a href="#english">English</a>
</p>

<p align="center">
  <img alt="Python" src="https://img.shields.io/badge/Python-3.10%2B-3776AB?logo=python&logoColor=white">
  <img alt="JavaScript" src="https://img.shields.io/badge/JavaScript-ES2020-F7DF1E?logo=javascript&logoColor=black">
  <img alt="License" src="https://img.shields.io/badge/License-MIT-2e6f4e">
  <img alt="PDF" src="https://img.shields.io/badge/PDF-49%20pages-a4442e">
</p>

---

## 中文

### 简介

PCMS-Kin 是一个**亲属关系代数 + 中文称呼生成**的实验性工程。它不把“亲戚”预先枚举成一张巨大的表，而是先把亲属关系写成二元关系，用十三条公理推出“父亲的妻子是母亲”“同胞的同胞是自己或同胞”这类等式，再把化简后的规范形翻译成中文称呼。

工程包含四个部分：

- **关系引擎**：生成元、链、复合、并、逆、化简与规范形；
- **命名引擎**：直系、旁系、姻亲、同性婚姻、深层“眷/姻”构词；
- **网页计算器**：快速计算、变量、关系转换，支持同性婚姻；
- **数学教科书**：把公理体系与称呼手册合并成 A4 PDF（49 页，含目录、书签、插图）。

### 核心特性

- **公理化**：13 条局部公理推出父母、同胞、长幼与十条化简等式。
- **可计算**：任何链先化简成六种规范形之一，再进入命名算法。
- **支持同性婚姻**：按“性别本位”外推，不把婚姻限定为异性。
- **深层姻亲**：用“段前缀 + 重锚”处理任意长的“眷/姻”链。
- **两条硬约束**：生成的称呼末位词必须满足 `辈分 = #P − #C`、`性别 = 末位生成元性别`。
- **双实现**：Python 引擎与 JavaScript 移植，长链输出逐字一致。
- **可验证**：对 1–6 段链穷举、对 6–10 段长链随机测试，未发现辈分/性别错位。

### 快速开始

#### 1. Python API

核心引擎不依赖第三方库，只需要 Python 3.10+。

```python
from generators import Parent, Mate, Elder
from naming import name_chain

# 父的母的姐的妻的兄的妻
gens = [
    Parent('m'), Parent('f'), Elder('f'),
    Mate('f'), Elder('m'), Mate('f'),
]
result = name_chain(gens)

print(result['formula'])   # PmPfEfMfEmMf
print(result['primary'])   # 姨祖眷舅祖母
print(result['names'])     # 结构化结果：monomial / primary / alternatives
```

也可以直接使用关系代数：

```python
from generators import Parent, Child
from kinship_formula import init, priority

formula = init([Parent('m'), Child('m')])
# 化简为「哥哥 / 自己 / 弟弟」三条规范形
```

#### 2. 网页计算器

```bash
python demo_server.py
# 打开 http://127.0.0.1:8756/demo/index.html
```

也可以直接双击打开 `demo/index.html`，无需服务器。

![网页计算器](docs/demo.png)

#### 3. 数学教科书 PDF

直接打开：

**[亲属关系的代数与命名.pdf](亲属关系的代数与命名.pdf)**

PDF 共 49 页，A4，包含：

- 第 1–3 章：关系代数、十三条公理、规范形与化简算法；
- 第 4–5 章：称呼的语法、段前缀与重锚、命名算法；
- 第 6 章：实现、验证、四个真实 BUG 的解剖；
- 附录 A–E：化简表、段前缀表、重锚表、术语表、Lean 4 验证；
- 6 幅插图、18 张表、可点击目录与 PDF 书签。

### 示例

| 链 | 中文关系 | 主呼称 |
|---|---|---|
| `Pm` | 父 | 爸爸 |
| `PmEmCm` | 父的兄的子 | 堂兄弟 |
| `PmEfMf` | 父的姐的妻 | 大姑媳（同性分支） |
| `PmPfEfMfEmMf` | 父的母的姐的妻的兄的妻 | 姨祖眷舅祖母 |
| `CmCfCfMfPmPfPfEmMfYf` | 子的女的女的妻的父的母的母的兄的妻的妹 | 曾外孙女眷舅曾祖眷妹 |
| `CmCmCmMmPmEm` | 曾孙的丈夫的父亲的哥哥 | 曾孙姻孙 |
| `MfPfEmMmPfPmPmEmCm` | 妻方深支 | 妻曾祖父 |

> “眷”表示中间配偶是女性，“姻”表示中间配偶是男性；“眷/姻”是段标记，不是“眷属”的泛称。

### 工作原理

整个系统分三层：

```text
关系层：P 父母 · C 子女 · M 配偶 · E 兄姐 · Y 弟妹
   │
   ▼
公理层：13 条局部事实 → 10 条化简等式 → 6 种规范形
   │
   ▼
命名层：直系 / 旁系 / 姻亲词法 → 段前缀 + 重锚 → 中文称呼
```

命名算法的核心是两条不变量：

```text
辈分(末位词) = #P − #C
性别(末位词) = 最后一个生成元的性别
```

算法先按配偶位置分派：

1. 末位是 `M` → **mate-last**（某人的配偶）；
2. 首位是 `M` → **mate-first**（配偶的亲属）；
3. 中间含 `M` → **mate-middle**：切第一个 `M`，用 `seg(X,g) + rname(g,s,Y)` 命名；
4. 都没有 → 直系或纯旁系词法。

对于“`Y` 中还有配偶”的嵌套情形，新锚点辈分为：

```text
s₂ = s + p(Y₁)
```

而不是直接沿用 `s`。这是修复“曾外孙女眷舅曾祖眷姨祖父”一类辈分错位的关键。

### 项目结构

```text
.
├── generators.py              # 生成元类
├── kinship_formula.py         # 关系代数、化简、辈分
├── naming.py                  # 词法表与命名算法
├── demo_server.py             # 本地网页服务器（标准库）
├── demo/
│   ├── index.html             # 网页计算器
│   └── kinship.js             # JavaScript 引擎与命名移植
├── 亲属关系公理.md             # 13 条公理与 Lean 4 验证
├── 亲属称呼手册.md             # 手工可查的称呼规则
├── 亲属关系的代数与命名.pdf    # 数学教科书（49 页）
├── book/                      # PDF 源文件与构建管线
│   ├── src/                   # 各章 HTML
│   ├── assets/                # 样式、KaTeX、SVG 插图
│   ├── figures.py             # matplotlib 插图
│   ├── build.js               # HTML + KaTeX 预渲染
│   ├── paginate.py            # 两遍分页，回填目录页码
│   ├── finalize.py            # PDF 元数据与书签
│   └── make.ps1               # 一键构建
├── manual_src/                # 手册分章源文件
├── docs/
│   ├── cover.png
│   └── demo.png
└── LICENSE
```

### 验证

验证不是只和 `relationship` 库对照，而是用一个独立检查器解析生成名的**末位词**，再与公式的辈分、性别比较。

| 测试 | 规模 | 结果 |
|---|---|---|
| 穷举全部 1–6 段链 | 1,111,110 条 | 0 处辈分/性别错位 |
| 随机 6–10 段长链（两组） | 150,000 + 50,000 条 | 0 处 |
| 上一轮失败的 6 段链复测 | 896 条 | 0 条剩余 |
| Python/JS 长链对照 | 305 条 | 逐字一致 |

更完整的验证方法、四个 BUG 的成因与修复见 PDF 第 6 章。

### 文档

- [亲属关系公理.md](亲属关系公理.md)：13 条公理、主要定理与 Lean 4 验证。
- [亲属称呼手册.md](亲属称呼手册.md)：可手算的称呼规则与速查表。
- [亲属关系的代数与命名.pdf](亲属关系的代数与命名.pdf)：数学教科书式总整理。
- [book/README.md](book/README.md)：PDF 的源文件结构与构建说明。

### 构建 PDF（可选）

需要 Node.js 24、Python 3.12 + `pymupdf`、Microsoft Edge，以及 Windows 自带的宋体/黑体。

```bash
pip install pymupdf
cd book
pnpm install
powershell -NoProfile -ExecutionPolicy Bypass -File .\make.ps1
```

产物会复制到项目根目录的 `亲属关系的代数与命名.pdf`。脚本会执行两遍分页：先打印草稿，定位每章实际页码，再重建目录并打印最终 PDF。

### 许可与致谢

本项目以 **MIT License** 发布，Copyright (c) 2026 Subaru Akuru。详见 [LICENSE](LICENSE)。

致谢：

- `mumuy/relationship`（Python 移植版）：中文亲属称谓词表与选择器；
- 《亲属关系公理》的 Lean 4 机器验证工作；
- KaTeX、Matplotlib、PyMuPDF、Microsoft Edge：PDF 排版与输出。

> 说明：本项目是“可计算优先”的形式化实验，不保证所有机械构词都是某地方言的真实说法；公理系统也不处理收养、继亲、离婚再婚等情形。边界讨论见 PDF 第 6.4 节。

---

## English

### Overview

PCMS-Kin is an experimental **kinship algebra + Chinese kinship-term generator**. Instead of storing a huge lookup table of relatives, it represents kinship relations as binary relations, derives identities such as “father's wife is mother” and “sibling's sibling is self or sibling” from thirteen axioms, and then translates the resulting normal forms into Chinese kinship terms.

The repository contains four parts:

- **Relation engine**: generators, chains, composition, union, inverse, normalization, and normal forms.
- **Naming engine**: direct, collateral, affinal, same-sex, and deep “眷/姻” (affinal-segment) terms.
- **Web calculator**: quick calculation, variables, relation conversion, and same-sex marriage support.
- **Textbook**: a 49-page A4 PDF that unifies the axiom system and the naming manual.

### Features

- **Axiomatic**: 13 local axioms imply the parent/sibling/age facts and ten simplification identities.
- **Computable**: every chain is normalized into one of six normal forms before naming.
- **Same-sex inclusive**: uses a “gender-first” extrapolation rather than assuming heterosexual marriage.
- **Deep affinal chains**: a segment-prefix + re-anchor algorithm handles arbitrarily long “眷/姻” chains.
- **Two hard invariants**: the final term must satisfy `generation = #P − #C` and `sex = sex of the last generator`.
- **Dual implementation**: Python engine and JavaScript port, with identical outputs on long chains.
- **Verified**: exhaustive testing of all chains up to length 6 and large random tests of length 6–10.

### Quick Start

#### Python API

The core engine has no third-party dependencies; Python 3.10+ is enough.

```python
from generators import Parent, Mate, Elder
from naming import name_chain

# father's mother's elder sister's wife's elder brother's wife
gens = [
    Parent('m'), Parent('f'), Elder('f'),
    Mate('f'), Elder('m'), Mate('f'),
]
result = name_chain(gens)

print(result['formula'])   # PmPfEfMfEmMf
print(result['primary'])   # 姨祖眷舅祖母
print(result['names'])     # structured: monomial / primary / alternatives
```

#### Web Calculator

```bash
python demo_server.py
# open http://127.0.0.1:8756/demo/index.html
```

You can also open `demo/index.html` directly; no server is required.

![Web calculator](docs/demo.png)

#### Textbook PDF

Open **[亲属关系的代数与命名.pdf](亲属关系的代数与命名.pdf)**.

The PDF is A4, 49 pages, and includes:

- Chapters 1–3: relation algebra, 13 axioms, normal forms and rewriting;
- Chapters 4–5: kinship-term grammar, segment prefix + re-anchor, naming algorithm;
- Chapter 6: implementation, verification, and four real bug case studies;
- Appendices A–E: simplification tables, segment-prefix tables, re-anchor tables, glossary, Lean 4 verification;
- 6 figures, 18 tables, clickable TOC, and PDF bookmarks.

### Examples

| Chain | Relation | Primary term |
|---|---|---|
| `Pm` | father | 爸爸 |
| `PmEmCm` | father's elder brother's son | 堂兄弟 |
| `PmEfMf` | father's elder sister's wife | 大姑媳 (same-sex branch) |
| `PmPfEfMfEmMf` | father's mother's elder sister's wife's elder brother's wife | 姨祖眷舅祖母 |
| `CmCfCfMfPmPfPfEmMfYf` | son's daughter's daughter's wife's father's mother's mother's elder brother's wife's younger sister | 曾外孙女眷舅曾祖眷妹 |
| `CmCmCmMmPmEm` | great-grandson's husband's father's elder brother | 曾孙姻孙 |
| `MfPfEmMmPfPmPmEmCm` | a deep wife-side branch | 妻曾祖父 |

> “眷” marks a female middle spouse; “姻” marks a male middle spouse. They are segment markers, not the everyday word “眷属”.

### How It Works

```text
Relation layer: P parent · C child · M mate · E elder sibling · Y younger sibling
   │
   ▼
Axiom layer: 13 local facts → 10 simplification identities → 6 normal forms
   │
   ▼
Naming layer: direct / collateral / affinal lexicon → segment prefix + re-anchor → Chinese term
```

The naming algorithm maintains two invariants:

```text
generation(final term) = #P − #C
sex(final term)        = sex of the last generator
```

Dispatch order:

1. last generator is `M` → **mate-last**;
2. first generator is `M` → **mate-first**;
3. `M` occurs in the middle → **mate-middle**: split at the first `M`, then use `seg(X,g) + rname(g,s,Y)`;
4. otherwise → direct or pure-collateral naming.

For nested spouses (`Y` itself contains `M`), the new anchor's generation is

```text
s₂ = s + p(Y₁)
```

rather than reusing `s`. This is the key fix for generation shifts such as “曾外孙女眷舅曾祖眷姨祖父”.

### Repository Layout

```text
.
├── generators.py             # generator classes
├── kinship_formula.py        # relation algebra, normalization, generation
├── naming.py                 # lexicon and naming algorithm
├── demo_server.py            # local static server (stdlib)
├── demo/
│   ├── index.html            # web calculator
│   └── kinship.js            # JavaScript engine and naming port
├── 亲属关系公理.md            # 13 axioms and Lean 4 verification
├── 亲属称呼手册.md            # hand-computable naming manual
├── 亲属关系的代数与命名.pdf   # 49-page textbook
├── book/                     # PDF sources and build pipeline
│   ├── src/
│   ├── assets/
│   ├── figures.py
│   ├── build.js
│   ├── paginate.py
│   ├── finalize.py
│   └── make.ps1
├── manual_src/
├── docs/
│   ├── cover.png
│   └── demo.png
└── LICENSE
```

### Verification

Rather than relying only on the `relationship` library, we use an independent checker: it parses the **final term** of each generated name and compares its generation and sex with the formula.

| Test | Scale | Result |
|---|---|---|
| Exhaustive, all chains of length 1–6 | 1,111,110 chains | 0 generation/sex mismatches |
| Random chains of length 6–10 (two runs) | 150,000 + 50,000 | 0 |
| Previously failing length-6 chains | 896 | 0 remaining |
| Python/JS long-chain comparison | 305 | character-identical |

See Chapter 6 of the PDF for the full methodology and four bug case studies.

### Documentation

- [亲属关系公理.md](亲属关系公理.md): axioms, main theorems, Lean 4 verification.
- [亲属称呼手册.md](亲属称呼手册.md): hand-computable naming rules and quick-reference tables.
- [亲属关系的代数与命名.pdf](亲属关系的代数与命名.pdf): the unified textbook.
- [book/README.md](book/README.md): PDF source layout and build instructions.

### Build the PDF (Optional)

Requires Node.js 24, Python 3.12 + `pymupdf`, Microsoft Edge, and Chinese fonts shipped with Windows.

```bash
pip install pymupdf
cd book
pnpm install
powershell -NoProfile -ExecutionPolicy Bypass -File .\make.ps1
```

The final PDF is copied to `亲属关系的代数与命名.pdf` in the project root. The script performs two passes: print a draft, locate the actual page number of every TOC entry, then rebuild the TOC and print the final PDF.

### License & Acknowledgements

Released under the **MIT License**, Copyright (c) 2026 Subaru Akuru. See [LICENSE](LICENSE).

Acknowledgements:

- `mumuy/relationship` (Python port) for the Chinese kinship vocabulary and selector;
- the Lean 4 formalization in 《亲属关系公理》;
- KaTeX, Matplotlib, PyMuPDF, and Microsoft Edge for PDF typesetting and output.

> This is a computability-first formalization experiment. Not every mechanical compound is a term used in everyday speech, and the axiom system does not model adoption, step-relations, divorce, or remarriage. See Section 6.4 of the PDF for the boundary discussion.
