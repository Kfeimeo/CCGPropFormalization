# CCGPropFormalization

Lean 4 / Mathlib 形式化与 **theorem audit**：

> FA/BA + unrestricted type raising + generalized composition ⇒ prefix reducibility

**结论先行（audit 结果）**

| 命题 | 结果 | Lean |
|---|---|---|
| 原命题：有完整 derivation ⇒ 每个非空前缀可规约到某个 category | **成立，但是平凡的**：假设根本用不到，结论对任意 lexicon 都成立，连"存在完整 derivation"这个假设本身也对任意 lexicon 恒成立 | `prefix_reducible_of_full_derivation`, `prefixReducible_full`, `exists_full_derivation` |
| 根本原因 | unrestricted TR（目标 `T` 任意）+ `B¹` 使**任意两个** category 都能组合：`A ⇒ T/(T\A)`, `B ⇒ (T\A)/((T\A)\B)`, 再 `B¹` 得 `T/((T\A)\B)` | `Rules.minimal_combine_any`, `Combine.any` |
| 去掉 TR | **不成立**。最小反例 `[X/Y, W, Y\W]`（n = 3）：整句推出 `X`，前缀 `X/Y W` 无法规约 | `not_prefixReducible_noTR` |
| TR 目标限制为原子 | **不成立**。反例 `[NP, NP, (S\NP)\NP]`：整句推出 `S`，前缀 `NP NP` 无法规约 | `not_prefixReducible_atomicTR` |
| 弱 normalization：完整 derivation ⇒ 存在 left-spine derivation（category 可不同） | 成立（同样平凡、无条件） | `weak_left_spine_normalization` |
| 强 normalization：`Derives 0 n C ⇒ LeftSpine 0 n C`（**同一个** category） | **不成立**，即使加上 backward composition、crossed composition、双向 TR。反例 "what John likes" `[S/(S/NP), NP, (S\NP)/NP]` 推出 `S`，但没有任何 left-branching derivation 推出 `S` | `not_strong_left_spine_normalization`, `lexWhat_not_strongPrefixReducible` |

整个项目 `lake build` 通过，无 `sorry`；核心定理只依赖 `propext`、`Quot.sound`（反例部分另含 `Classical.choice`，来自 Mathlib 引理）。

---

## 目录

1. [形式系统](#1-形式系统)
2. [generalized composition 的 Lean 表示](#2-generalized-composition-的-lean-表示)
3. [theorem 是否原样成立](#3-theorem-是否原样成立)
4. [theorem audit：缺失的条件与反例](#4-theorem-audit缺失的条件与反例)
5. [最终证明了什么](#5-最终证明了什么)
6. [构建与文件结构](#6-构建与文件结构)
7. [设计决策说明](#7-设计决策说明)

---

## 1. 形式系统

所有定义在命名空间 `CCG` 下。

### Category（`Cat.lean`）

```lean
inductive Cat (Atom : Type)
  | atom : Atom → Cat Atom
  | fwd  : Cat Atom → Cat Atom → Cat Atom   -- X/Y   记作 X ⫽ Y
  | bwd  : Cat Atom → Cat Atom → Cat Atom   -- X\Y   记作 X ⧵ Y
```

`⫽`、`⧵` 左结合：`X ⫽ Y ⫽ Z = (X/Y)/Z`。原子类型 `Atom` 是参数（例子中用 `At = {s, np, n}`）。

`Slash := fwd | bwd` 与 `Cat.slash X s Y` 统一表示 `X | Y`（任一方向的 slash），配套引理 `slash_eq_fwd_iff`、`slash_eq_bwd_iff`、`slash_ne_atom` 用于反演。

### Type raising（`Rules.lean`）

```lean
inductive TypeRaise : Cat Atom → Cat Atom → Prop
  | fwd (T A) : TypeRaise A (T ⫽ (T ⧵ A))   -- A ⇒ T/(T\A)
  | bwd (T A) : TypeRaise A (T ⧵ (T ⫽ A))   -- A ⇒ T\(T/A)
```

目标 `T` 完全自由，这就是 "unrestricted"。

### 二元规则（`Rules.lean`）

```lean
inductive Combine : Cat Atom → Cat Atom → Cat Atom → Prop
  | fa (X Y)    : Combine (X ⫽ Y) Y X                       -- X/Y  Y  ⇒ X
  | ba (X Y)    : Combine Y (X ⧵ Y) X                       -- Y  X\Y  ⇒ X
  | fcomp s Z   : ReplaceHead Y X A B → Combine (X ⫽ Y) (A.slash s Z) (B.slash s Z)
                                                            -- X/Y  Y|Z₁…|Zₙ ⇒ X|Z₁…|Zₙ (n ≥ 1)
  | bcomp s Z   : ReplaceHead Y X A B → Combine (A.slash s Z) (X ⧵ Y) (B.slash s Z)
                                                            -- Y|Z₁…|Zₙ  X\Y ⇒ X|Z₁…|Zₙ (n ≥ 1)
```

`Combine.fcomp₁ : Combine (X ⫽ Y) (Y ⫽ Z) (X ⫽ Z)` 是普通的 `B¹`。

### 规则集与 derivation（`Derivation.lean`）

为了让 audit 精确，`Derives` 以规则集 `Rules := ⟨tr, bin⟩` 为参数：

| 规则集 | `tr` | `bin` | 用途 |
|---|---|---|---|
| `Rules.full` | `TypeRaise`（双向、目标任意） | `Combine`（FA/BA/前后向广义组合） | 原命题所在系统 |
| `Rules.minimal` | 仅前向 TR，目标任意 | 仅 `B¹` | 正面结果的**最小**规则集 |
| `Rules.noTR` | 无 | `Combine` | audit 1 |
| `Rules.atomicTR` | 双向 TR，目标必须是原子 | `Combine` | audit 3 |

`Rules` 上有偏序 `≤`（逐点包含），`Derives.mono` / `LeftSpine.mono` 保证正面结果向上传递、反例向下传递。

```lean
inductive Derives (R : Rules Atom) (lex : Fin n → Cat Atom) : ℕ → ℕ → Cat Atom → Prop
  | lex (i : Fin n) : Derives R lex i (i+1) (lex i)                          -- lexical item
  | tr  : Derives R lex i j C → R.tr C D → Derives R lex i j D               -- type raising（任意节点）
  | bin : Derives R lex i k A → Derives R lex k j B → R.bin A B C → Derives R lex i j C
```

`Derives R lex i j C`：连续区间 `[i, j)` 可规约为 `C`。TR 允许作用在任何成分上（不只 lexical item）。

```lean
inductive LeftSpine (R) (lex) : ℕ → ℕ → Cat Atom → Prop      -- (((w₁ w₂) w₃) ⋯ wₙ)
  | lex (i : Fin n) : LeftSpine R lex i (i+1) (lex i)
  | tr  : LeftSpine R lex i j C → R.tr C D → LeftSpine R lex i j D
  | bin : LeftSpine R lex i j A → LeftSpine R lex j (j+1) B → R.bin A B C → LeftSpine R lex i (j+1) C
```

每个二元节点的右孩子都是单个（可 TR 的）词，即 left-branching / 从左到右的增量 derivation。`LeftSpine.toDerives : LeftSpine ⊆ Derives`。

### Prefix reducibility

```lean
def PrefixReducible (R) (lex : Fin n → Cat Atom) : Prop :=
  ∀ i, 0 < i → i ≤ n → ∃ C, Derives R lex 0 i C

-- 强版本：前缀的 category 要与最终 category C 兼容（一步就能与剩余部分合并成 C）
def StrongPrefixReducible (R) (lex) (C : Cat Atom) : Prop :=
  ∀ i, 0 < i → i < n → ∃ P D, Derives R lex 0 i P ∧ Derives R lex i n D ∧ R.bin P D C
```

## 2. generalized composition 的 Lean 表示

不枚举 `B¹, B², …`，而是定义"替换 head"关系（`Cat.lean`）：

```lean
inductive ReplaceHead (Y X : Cat Atom) : Cat Atom → Cat Atom → Prop
  | refl : ReplaceHead Y X Y X                                            -- n = 0
  | step (s : Slash) (Z) : ReplaceHead Y X A B → ReplaceHead Y X (A.slash s Z) (B.slash s Z)
```

`ReplaceHead Y X A B` 读作 `A = Y|Z₁|⋯|Zₙ`，`B = X|Z₁|⋯|Zₙ`（同样的 slash、同样的参数，只把最内层 head `Y` 换成 `X`）。这正是题目中的
`replaceHead(Y, X, Y|Z₁|⋯|Zₙ) = X|Z₁|⋯|Zₙ`。它等价于对同一个 spine 列表做折叠：

```lean
theorem ReplaceHead.iff_spine :
    ReplaceHead Y X A B ↔ ∃ sp : List (Slash × Cat Atom), A = Y.spine sp ∧ B = X.spine sp
```

广义前向组合 `Bⁿ`（`n ≥ 1`）定义为

```lean
| fcomp (s : Slash) (Z) : ReplaceHead Y X A B → Combine (X ⫽ Y) (A.slash s Z) (B.slash s Z)
```

`ReplaceHead` 负责内层的 `n-1` 个参数，最外层 `|Zₙ` 由 `slash s Z` 给出，保证 `n ≥ 1`（`n = 0` 就是 FA，单独作为 `fa` 规则）。spine 中的 slash 可以任意混合，所以 `fcomp` 同时覆盖 harmonic 与 crossed 的实例（`Examples.lean` 里有 `B²`、混合 spine 的 `B³`、`B¹ₓ` 的例子）。

## 3. theorem 是否原样成立

**成立**。`Positive.lean`：

```lean
theorem prefix_reducible_of_full_derivation (lex : Fin n → Cat Atom)
    (h : ∃ C, Derives Rules.full lex 0 n C) : PrefixReducible Rules.full lex
```

但证明**完全不使用 `h`**。真正的内容是下面这条链：

1. `Rules.minimal_combine_any`：任意 `A B`，取 `A' = A/(A\A)`，`B' = (A\A)/((A\A)\B)`（都是前向 TR，目标分别是 `A` 和 `A\A`），`B¹` 得到 `A/((A\A)\B)`。
2. `LeftSpine.exists_minimal`：对 `j` 归纳，任意区间 `[i, j)` 都有一个 left-spine derivation（每次把已有前缀与下一个词按 1 组合）。
3. `prefixReducible_of_le`：任何包含 `Rules.minimal` 的规则集都无条件 prefix reducible；`Rules.minimal ≤ Rules.full` 得 `prefixReducible_full`。
4. `exists_full_derivation`：同理，假设 `∃ C, Derives Rules.full lex 0 n C` 对任何 `n > 0` 的 lexicon 恒真。

换言之，在 "unrestricted TR" 的字面定义下，命题的前提与结论都是恒真式：`NP NP NP` 这样的 word salad 也有"完整 derivation"、也是 prefix reducible（`Examples.lean`）。定理本身没有讲出任何关于 CCG derivation 结构的事实——这正是 audit 要指出的：**unrestricted TR 相当于把 "任意两个成分可合并" 直接编码进了规则**，与题目第 8 点禁止的"把 prefix reducibility 编码进规则"实质相同，只不过是通过 TR 目标的任意性间接完成的。

## 4. theorem audit：缺失的条件与反例

原命题不是假的，所以不存在需要"修正"的错误；audit 的任务变成回答两个问题：(a) 命题为真到底靠什么条件；(b) 有没有一个**非平凡**的正确版本。三个反例分别回答。

### Audit 1：去掉 TR，命题为假（`Audit/NoTR.lean`）

最小反例（`n = 3`；`n ≤ 2` 时真前缀只有单词，命题平凡）：

```
w₁ = X/Y    w₂ = W    w₃ = Y\W        (原子，W ≠ Y)
```

- 整句：`W  Y\W ⇒ Y`（BA），`X/Y  Y ⇒ X`（FA）。`lexNoTR_full`
- 前缀 `X/Y  W`：FA 需要 `W = Y`；BA 需要 `W` 是 `_\(X/Y)`；两种组合需要 `W` 是函子。都不可能。`lexNoTR_prefix_irreducible`

结论：`not_prefixReducible_noTR`。**缺失的条件正是 TR**。而且要让这个前缀可规约，需要 `W ⇒ Y/(Y\W)` 再 `B¹`——TR 的目标 `Y` 是由**后文** `w₃` 决定的（`lexNoTR_prefix_reducible_with_TR`）。这解释了为什么"unrestricted"是命题为真的关键。

### Audit 3：TR 目标限制为原子，命题为假（`Audit/AtomicTR.lean`）

要避免平凡化，自然的想法是限制 TR 目标。最保守的限制（目标只能是原子，如 `NP ⇒ S/(S\NP)`）已经让命题失效：

```
w₁ = NP    w₂ = NP    w₃ = (S\NP)\NP
```

- 整句：两次 BA 推出 `S`（不需要 TR）。`lexAtomic_full`
- 前缀 `NP NP`：`lexAtomic_no_combine` 证明两个（任意多次、原子目标）type-raised 的 `NP` 不能被任何二元规则合并（对 TR 闭包做归纳 + 对最后一条规则做穷举）。

结论：`not_prefixReducible_atomicTR`。合起来：**命题的真假恰好等于 TR 目标是否允许复合 category**——允许则平凡为真，不允许则为假。不存在一个对所有 lexicon 都成立的"非退化"读法。

### Audit 2：强版本为假（`Audit/Strong.lean`）

题目第 10 点希望把证明建立为 normalization / reassociation 定理。弱形式（`∃ C', LeftSpine 0 n C'`）无条件成立（`weak_left_spine_normalization`），同样平凡。有意义的是强形式：

> `Derives lex 0 n C → LeftSpine lex 0 n C`（**同一个** `C`），或等价地 `StrongPrefixReducible`。

它**不成立**。反例是宾语提取 "what John likes"：

```
w₁ = S/(S/NP)    w₂ = NP    w₃ = (S\NP)/NP
```

- 右分支 derivation：`NP ⇒ S/(S\NP)`（TR），`S/(S\NP)  (S\NP)/NP ⇒ S/NP`（`B¹`），`S/(S/NP)  S/NP ⇒ S`（FA）。`lexWhat_full`
- 不存在 `(w₁ w₂) w₃` 形式的推导得到 `S`：`lexWhat_no_compatible_prefix`。证明思路：
  1. 最后一步要得到原子 `S`，只能是 FA 或 BA（组合结果永远带 spine），且 `w₃` 侧是 `(S\NP)/NP` 的 TR 闭包，于是前缀 category 必须是 `S/u`，`u ∈ TR*((S\NP)/NP)`（"good"）。
  2. good 沿 TR 向前传递（`lexWhat_good_of_trstar`），所以 `w₁' w₂'` 一步组合的结果就得是 good。
  3. 对 `w₁' ∈ TR*(S/(S/NP))`、`w₂' ∈ TR*(NP)` 和四条二元规则穷举，配合三条沿 TR 闭包的归纳引理（`lexWhat_aux_np`、`lexWhat_aux_a₁`、`lexWhat_aux_a₂`），每种情形都矛盾。
- 于是 `¬ LeftSpine … 0 3 S`（`lexWhat_no_leftSpine`）与 `¬ StrongPrefixReducible … S`。

这个反例对**加规则**是稳健的：证明在 `Rules.full` 上进行，已包含 backward composition、crossed composition 和双向 TR（任意节点）；由 `mono`，任何子规则集也不行。一般地，reassociation 引理在 `A = X/(Y|Zs)`、而 `B' u` 通过组合产出 `Y|Zs` 时失效——`A` 的参数是函子，而 left-branching 只能把 `A` 和 `B'` 先合并，`B'` 的 head 与 `A` 要求的参数不匹配。

### 关于"最弱的修正版"

- 原命题（弱形式）不需要修正：它成立，且可以**去掉假设**并**缩小规则集**到 `Rules.minimal`（前向 TR + `B¹`），这是最强的正确加强（`prefixReducible_of_le`）。
- 想让它变得非平凡，只能限制 TR；但 audit 1 与 3 说明**任何**把目标限制到原子的做法都会让它变假，而允许复合目标又立即回到平凡。
- 想让它变得有用（前缀 category 与整句兼容 / 同 category 的 left-spine 归一化），audit 2 说明在 FA/BA/广义组合/TR 这套规则下对任意 lexicon 不可能成立；它只在特定 lexicon 上成立（如 `John likes Mary`，见 `Examples.lean`），要得到一般定理必须换规则系统（例如 Pareschi–Steedman 的 revealing）或限制 lexicon，这超出了本题的规则集，本项目不作猜测性加强。

## 5. 最终证明了什么

正面（`Positive.lean`）：

| 定理 | 内容 |
|---|---|
| `Rules.minimal_combine_any`, `Combine.any` | 任意两个 category 经前向 TR + `B¹` 可合并 |
| `LeftSpine.exists_minimal`, `LeftSpine.exists_of_le`, `Derives.exists_of_le` | 任意区间 `[i, j)` 都有 left-spine derivation（任意 lexicon） |
| `prefixReducible_of_le`, `prefixReducible_full` | 无条件 prefix reducibility |
| `prefix_reducible_of_full_derivation` | **原命题**（作为推论，假设未用） |
| `exists_full_derivation` | 原命题的假设恒真 |
| `weak_left_spine_normalization` | `Derives 0 n C → ∃ C', LeftSpine 0 n C'` |

反面：

| 定理 | 内容 |
|---|---|
| `not_prefixReducible_noTR` | 无 TR：`[X/Y, W, Y\W]` 有完整 derivation 但不 prefix reducible |
| `not_prefixReducible_atomicTR` | 原子目标 TR：`[NP, NP, (S\NP)\NP]` 同上 |
| `lexWhat_no_compatible_prefix`, `lexWhat_not_strongPrefixReducible` | "what John likes" 的前缀没有与 `S` 兼容的 category |
| `not_strong_left_spine_normalization` | `Derives 0 3 S ∧ ¬ LeftSpine 0 3 S` |

基础设施（`Cat.lean`, `Rules.lean`, `Derivation.lean`）：`ReplaceHead.iff_spine`、`Combine.inv`、`Derives.lt_and_le`、`Derives.mono`、`Derives.congr`（derivation 只看区间内的词）、`Derives.single`、`Derives.two`、`LeftSpine.toDerives`、`LeftSpine.inv`。

例子（`Examples.lean`）：`John likes Mary` 上的 FA、BA、TR（双向）、`B¹`、`B²`、混合 spine 的 `B³`、crossed `B¹ₓ`、backward composition、left-spine derivation，以及所有主定理/反例在具体原子类型上的实例。

## 6. 构建与文件结构

```
lake build          # Lean 4 v4.33.1, Mathlib v4.33.1；建议先 lake exe cache get
```

```
CCGPropFormalization.lean            -- 根模块
CCGPropFormalization/
  Cat.lean                           -- Cat, Slash, slash, spine, ReplaceHead
  Rules.lean                         -- TypeRaise, Combine, Rules (full / noTR / minimal), Combine.inv
  Derivation.lean                    -- Derives, LeftSpine, PrefixReducible, StrongPrefixReducible, 反演引理
  Positive.lean                      -- 正面结果（含原命题）
  Audit/NoTR.lean                    -- audit 1：无 TR 反例
  Audit/AtomicTR.lean                -- audit 3：原子目标 TR 反例
  Audit/Strong.lean                  -- audit 2："what John likes"，强版本反例
  Spine.lean                         -- 第二轮：flattenSpine / rebuildSpine / ArgSlot
  ASP.lean                           -- 第二轮：ASP、AdjacentSwap、Rules.appAsp / appCompAsp / withASP
  Audit/ASP.lean                     -- 第二轮：audit 4，FA/BA(+Bⁿ)+ASP 的反例与正面引理
  Examples.lean                      -- S/NP 例子与实例（含 ASP 的 decide 例子）
```

## 7. 设计决策说明

- **`lex : Fin n → Cat Atom`**，区间用 `ℕ` 下标，`Derives.lt_and_le` 保证 `i < j ≤ n`；`Derives.congr` 说明 derivation 只依赖区间内的词。
- **TR 作用在任意节点**（不只是 lexical item），与题目第 5 点一致；负面结果因此更强。
- **backward composition 与 crossed 实例**：正面证明不需要它们（只用 `Rules.minimal`），按题目要求没有"无理由加入"到正面结果里；它们放进 `Rules.full` 的唯一理由是让反例对更大的规则集也成立（`Audit/Strong.lean` 的穷举显式处理了 `bcomp` 与任意 slash 的 spine）。由 `mono`，所有反例对 `Rules.full` 的任何子集都成立。
- **反例不依赖原子互异**（除 audit 1 需要 `W ≠ Y`），全部以任意 `Atom` 为参数陈述，再在 `Examples.lean` 中实例化。
- **不含 `sorry`**；`#print axioms` 只出现 `propext`、`Quot.sound`（与反例中的 `Classical.choice`）。
- 第二轮起 `Rules` 的一元规则字段改名为 `unary`（`Rules.full.unary = TypeRaise`，`Rules.appAsp.unary = ASP`），`Derives.unary` 相应改名；语义不变。


---

# 第二轮：Argument-Spine Permutation (ASP)

新增文件 `Spine.lean`、`ASP.lean`、`Audit/ASP.lean`。本轮只做语法层；ASP 是显式的结构变换 `C ⇒_ASP C'`，在 `Derives` 中作为一条一元规则出现，**不是** category 相等。

**结论先行**

| 命题 | 结果 | Lean |
|---|---|---|
| `FA/BA + ASP` ⇒ prefix reducibility | **不成立** | `not_prefixReducible_appAsp` |
| `FA/BA + generalized composition + ASP` ⇒ prefix reducibility | **不成立**，同一个反例 | `not_prefixReducible_appCompAsp` |
| 最小反例 | `NP NP (S\NP)\NP`（n = 3，无附加条件）；另有 `S/S NP S\NP`（需 `NP ≠ S`） | `lexSOV_*`, `lexAdv_*` |
| 再加原子目标 TR 也不够 | **不成立** | `not_prefixReducible_atomicTRAsp` |
| ASP 是否退化为"任意两个 category 可组合" | **否**：两个原子永远不能组合 | `not_asp_combine_any`, `Combine.not_atom_atom` |
| ASP 买到了什么 | `A (F B) ⇒ (A F) B` 的重结合；`John likes Mary` 可从左到右推导 | `Derives.asp_reassoc`, `lexSVO_leftSpine` |
| ASP 带来的新退化 | 同一 functor 的所有 valency 顺序等价：`(X/A)/B` 也能接受 `F A B` 语序 | `lexVAB_full_appAsp` vs `lexVAB_prefix_irreducible_app` |

## A. Argument spine（`Spine.lean`）

```lean
abbrev Dir := Slash
structure ArgSlot (Atom) where (dir : Dir) (arg : Cat Atom)

def flattenSpine : Cat Atom → Cat Atom × List (ArgSlot Atom)
  | atom a  => (atom a, [])
  | X ⫽ A   => ((flattenSpine X).1, (flattenSpine X).2 ++ [⟨fwd, A⟩])
  | X ⧵ A   => ((flattenSpine X).1, (flattenSpine X).2 ++ [⟨bwd, A⟩])

def rebuildSpine (X) : List (ArgSlot Atom) → Cat Atom
  | []      => X
  | s :: sl => rebuildSpine (X.slash s.dir s.arg) sl
```

只沿 result/head spine 展开，slot 按由内到外排列；argument 内部**绝不**递归：

- `((X\A)/B)/C ↦ (X, [(bwd,A),(fwd,B),(fwd,C)])`
- `X\(A/B) ↦ (X, [(bwd, A/B)])`

已证：`rebuild_flatten`（`rebuildSpine (flattenSpine C).1 (flattenSpine C).2 = C`）、`flatten_rebuild`（converse/normalization：`flattenSpine (rebuildSpine X sl) = (head X, slots X ++ sl)`）、`flattenSpine_head_isAtom`（head 总是原子）、`flattenSpine_injective`、`flattenSpine_eq_iff`。并与第一轮的 `Cat.spine` / `ReplaceHead` 打通：`rebuildSpine_eq_spine`、`ReplaceHead.iff_rebuild`（广义组合 = 换 head、保留全部 slot）。

## B. 十个问题的回答

**1. ASP 的正式定义是什么？**

```lean
def ASP (C C' : Cat Atom) : Prop :=
  (flattenSpine C).1 = (flattenSpine C').1 ∧ List.Perm (flattenSpine C).2 (flattenSpine C').2
```

`ASP.iff_exists` 证明它与题目给出的 `∃ X args args', flattenSpine C = (X, args) ∧ flattenSpine C' = (X, args') ∧ args ~ args'` 等价。`ASP.refl / symm / trans / equivalence`：等价关系。不变量：`head_eq`、`perm`、`multiset_eq`（slot 的 multiset 不变）、`spineLength_eq`（valency 不变）、`slot_mem`（`C'` 的每个 slot 原封不动来自 `C`）。有 `DecidableRel` 实例，具体例子可用 `decide` 判定。

**2. 为什么它等价于 argument-spine permutation？**

`flattenSpine` 是 `Cat` 到 `Atom × List ArgSlot` 的双射（`rebuild_flatten` + `flatten_rebuild_atom`），所以"同 head、slot 列表互为置换"就是"外层 argument spine 任意置换"。更进一步，`perm_iff_rtg_adjacentSwap` 证明任意 `List.Perm` 是有限次相邻交换 `AdjacentSwap` 的复合，于是 `ASP.iff_rtg_step`：

```lean
ASP C C' ↔ Relation.ReflTransGen ASPStep C C'
```

其中 `ASPStep` 只交换两个**相邻** slot。ASP 不是无穷多条 primitive rule，而是一条局部交换规则的自反传递闭包。

**3. 为什么 `/A` 与 `\A` 必须作为完整 slot 一起移动？**

方向说明该 argument 出现在哪一侧，argument 说明它是什么；两者拆开就会改变一个 functor 的选择关系。形式上 slot 类型是 `ArgSlot = (dir, arg)`，置换在这个类型的列表上进行。`ASP.not_dir_swap` 证明"只交换 slash、不交换 argument"的 `(X\A)/B ↦ (X/A)\B` 在 `A ≠ B` 时不是 ASP；`Examples.lean` 里 `¬ ASP ((S⧵NP)⫽N) ((S⫽NP)⧵N)` 由 `decide` 判定。

**4. `/`–`/`、`\`–`\`、`/`–`\` 是否都可交换？**

都可以：`ASP.fwd_fwd`、`ASP.bwd_bwd`、`ASP.bwd_fwd` 都是同一个 `ASP.swap_outer X d₁ A d₂ B` 的实例；配合 `ASP.slash_congr` 得到内层交换如 `((X\A)/B)/C ⇔ ((X/B)\A)/C`（`ASP.bwd_fwd_fwd`）。ASP 对 slash 方向是盲的。

**5. `FA/BA + ASP` 是否推出 prefix reducibility？** 否。

**6. 最小反例是什么？**

`n = 3`（`n ≤ 2` 时真前缀都是单词）：

```
John : NP    Mary : NP    loves : (S\NP)\NP        —— lexSOV
```

整句两次 BA 推出 `S`（`lexSOV_full`）；前缀 `NP NP` 什么都推不出（`lexSOV_prefix_irreducible`）：ASP 固定原子（`ASP.eq_of_atom`），而两个原子不满足任何二元规则（`Combine.not_atom_atom`）。不需要任何原子互异的条件。第二个自然反例是英语句 `maybe John left = S/S NP S\NP`（`lexAdv`）：`S/S` 只有一个 slot，ASP 对它是恒等（`ASP.eq_of_atom_fwd`），前缀 `S/S NP` 在 `NP ≠ S` 时卡死。

**7. `FA/BA + generalized composition + ASP` 是否推出？** 否。两个反例都直接在 `Rules.appCompAsp`（FA/BA + 任意阶前后向广义组合 + ASP）上证明，再由 `Derives.mono` 传给 `Rules.appAsp`。失败结构：卡住的两个词都是**argument**（`NP NP`），或者是"functor + 它不选择的 argument"（`S/S NP`）。ASP 只能重排**一个 functor 自己的 valency**，不能给 argument 制造 valency，也不能改变它与尚未出现的 functor 之间的 constituent–constituent dependency。它不属于 embedded functional argument 或 crossed dependency 的问题：反例里所有 argument 都是原子、依赖全部投射。

**8. 是否还需要其他 structural rule？**

需要一条能把 argument 变成 functor 的规则，也就是 TR。而且目标必须允许复合 category：`not_prefixReducible_atomicTRAsp` 证明在 `FA/BA + Bⁿ + 原子目标 TR + ASP`（`Rules.atomicTRAsp`）下 `NP NP (S\NP)\NP` 仍然卡死——原子目标 TR 产出的都是单 slot functor，ASP 对它们是恒等（`TRAtom.spineLength_le_one`, `Rules.atomicTRAsp_unary_rtg`）。一旦允许复合目标，就回到第一轮的平凡化。ASP 与 TR 处理的是两个正交的问题：ASP 处理"同一 functor 的 argument 顺序"，TR 处理"argument 与 functor 的角色互换"。

**9. 与 unrestricted TR 相比，ASP 是否避免了退化？**

是。`Combine.any` 在 TR 下让任意两个 category 可组合；`not_asp_combine_any` 证明 ASP 下不存在这种通用组合（两个原子永远不能组合）。ASP 保持 head、valency 与 slot multiset，一个 category 的 ASP 类是有限的（`spineLength` 个 slot 的置换）。

**10. ASP 本身是否导致新的退化？**

有，而且是刻意的：同一 functor 的所有 valency 顺序在语法上等价。语法后果是同向 argument 的语序自由：`(X/A)/B` 在标准 CCG 中只接受 `F B A`，加上 ASP 后 `F A B` 也推出 `X`（`lexVAB_full_appAsp`），而不加 ASP 时前缀 `(X/A)/B A` 卡死（`lexVAB_prefix_irreducible_app`）。谁是主语、谁是宾语这类角色信息在本轮纯语法层无法区分，这正是下一轮要用 lambda-argument permutation 同步处理的内容。ASP 不改变 head，不改变 slash 方向，不进入 argument（`ASP.eq_of_atom_slash`：`X\(A/B)` 是 ASP 不动点；`ASP.arg_mem`：每个 argument category 原样保留），所以它不会把不同 head 或不同方向的 category 混同。

## C. Derives 中的开关

`Rules` 的一元字段现为 `unary`，ASP 作为一元规则加入：

| 规则集 | `unary` | `bin` |
|---|---|---|
| `Rules.app` | 无 | `App`（仅 FA、BA） |
| `Rules.appAsp` | `ASP` | `App` |
| `Rules.appCompAsp` | `ASP` | `Combine`（FA、BA、任意阶广义组合） |
| `R.withASP` | `R.unary ∨ ASP` | `R.bin` |

`Rules.appAsp` 与 `Rules.app.withASP` 互相 `≤`（`appAsp_le_withASP_app`, `withASP_app_le_appAsp`），`appCompAsp` 与 `noTR.withASP` 同理。TR 在这两个规则集中关闭；ASP 没有编码进 lexical category 或二元规则，`Derives.unary` 是唯一入口。

## D. 正面结果

- `Derives.asp_reassoc`：对任意 `R ⊇ appAsp`，若 `[i,k) ⇒ A`、`[k,j) ⇒ (H\A)/B`、`[j,l) ⇒ B`，则 `[i,j) ⇒ H/B` 且 `[i,l) ⇒ H`。这是 ASP 的核心用途：一个 functor 先吃哪个 argument 可以对调。
- `lexSVO_prefix₂ / lexSVO_leftSpine / lexSVO_prefixReducible`：`John likes Mary` 在 `FA/BA + ASP` 下 `John likes ⇒ S/NP`，整句 left-branching 推出 `S`，prefix reducible。
