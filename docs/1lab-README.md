# 1Lab

这是一个形式化的、相互关联的同伦类型论数学参考资源。与《同伦类型论》一书不同，1lab 并非"线性"资源：概念以有向图的形式呈现，链接表示依赖关系。

## 建筑

构建 1Lab 是一项相当复杂的任务，因此需要为其开发大量的自研基础设施。我们基于特定版本的 Mikan 进行构建（参见 `support/nix/haskell-packages.nix` 中的 fetchgit 参数），此外还有不少外部依赖项（例如 pdftocairo、katex）。推荐的 1Lab 构建方式是使用 Nix。

作为快速参考，nix-build程序将对整个文件进行类型检查和编译，并将必要的资源复制到正确的位置。结果将以链接形式提供./result，然后可用于提供网站服务：

```bash
$ nix-build
$ python -m http.server --directory result # e.g.
```

请注意，使用 Nix 构建网站大约需要 15 分钟，因为它每次都会从头开始对整个代码库进行类型检查。对于交互式开发，nix-shell它会提供一个包含您在 1Lab 上进行开发所需的一切的 shell，包括 Mikan 和预构建的 Shakefile，如下所示1lab-shake：

```bash
$ 1lab-shake all -j
```

由于nix-shell会将派生步骤加载为环境变量，因此您可以使用类似这样的方法将静态资源复制到相应位置：

```bash
$ eval "$installPhase"
$ python -m http.server --directory _build/site # e.g.
```

要持续修改文件，可以使用"监视模式"，该模式只会尝试检查和构建已更改的文件。

```bash
$ 1lab-shake all -w
```

此外，由于 Mikan 代码的有效性通常由 agda-mode 维护，因此您可以--skip-agda仅使用它来构建散文部分。请注意，这将禁用链接目标完整性检查和 span 的翻译`ref`{.Agda}，并且代码块会显得非常难看。

我们的构建工具通常会针对 x86_64-linux 进行构建并上传到 Cachix。如果您已安装 Cachix 命令行界面 (CLI)，只需运行即可cachix use 1lab。否则，请将以下内容添加到您的 Nix 配置中：

```
substituters = https://1lab.cachix.org
trusted-public-keys = 1lab.cachix.org-1:eYjd9F9RfibulS4OSFBYeaTMxWojPYLyMqgJHDvG1fs=
```

如果你需要修改 Shakefile 本身，nix-shell -A shakefile 它会提供一个包含所有必需 Haskell 依赖项和可用 Haskell 语言服务器安装的 shell。然后你可以使用它 cabal run 1lab-shake -- all -j来构建 Shakefile 和 1Lab。

## 直接地

如果你胆子够大，可以尝试复现上面提到的某个构建环境。你需要：

- 软件包管理器已停止cabal-install使用。stack
- 一个可正常运行的 LaTeX 安装（TeXLive 等），以及 default.nix 中列出的软件包 `our-texlive`。
- 波普勒（用于pdftocairo）
- Dart Sass（用于sass）
- Node.js节点及所需的 Node.js 模块。运行npm ci此命令进行安装。

然后，您可以使用 cabal-install 构建并运行我们特定版本的 Mikan 和 Shakefile。请按照说明cabal.project将 Mikan 锁定到合适的版本，然后运行：

```bash
$ cabal install Mikan -foptimise-heavily
# This will take quite a while!

$ cabal run 1lab-shake -- -j --skip-agda all
# the double dash separates cabal-install's arguments from our
# shakefile's.
```

要完成网站的构建，您还需要手动安装所需的资源：请installPhase参阅default.nix。

## 参与其中

我们的宗旨是让所有对数学感兴趣的人都能接触到单一价值的数学，无论其文化背景、年龄、教育背景、种族、性别认同或性别表达如何。HoTT 面向所有人开放，我们致力于营造一个友善、包容的环境。

1Lab 是一个社区项目。您可以在GitHub上贡献代码，也可以在Libera Chat#1lab频道与我们交流。我们欢迎所有贡献，但恳请您先与我们沟通，讨论并完善更重要的贡献方案。

我们欢迎所有数学领域的投稿，不仅限于已收录的领域或上述列出的领域。我们目前在实分析领域缺乏成果，并非因为我们禁止收录实分析，而是因为该领域并非我们任何作者的专长。我们乐于帮助任何人将他们感兴趣的主题形式化并撰写文章，但请记住，发展所有相关的理论基础可能是一项艰巨的任务。

## 技术

如果没有众多其他免费开源项目，1Lab 将无法实现。我们在此特别提及以下几个开源项目，因为它们至关重要：

- 字体：我们选用Julia Mono等宽字体（许可协议），因为它具有出色的 Unicode 覆盖率。文本内容可根据用户喜好选择使用Inria Sans（许可协议）或EB Garamond（许可协议）显示。所有这些字体均遵循SIL 开源字体许可协议 v1.1的条款进行分发。
- 散文：我们使用 Markdown 编写文本内容，并使用Pandoc进行渲染，然后通过各种过滤器来实现图表、折叠公式、高亮显示 div/详细信息等功能。尽管我们广泛使用 Pandoc，但项目的任何部分都不会分发。
- 数学公式：我们在编译时使用KaTeX排版数学公式。虽然渲染是预先完成的，但我们仍然会分发其 CSS 和字体。KaTeX 采用 MIT 许可证发布：许可证副本可在此处获取。
- 图标：我们的网站图标是来自Noto Emoji的冰块表情符号，该表情符号根据 Apache License 2.0 许可发布；您可以在这里找到副本。其他图标来自octicons，该表情符号根据 MIT 许可发布，您可以在这里找到。
- 图表：我们的图表使用quiver创建，并使用LaTeX和pdftocairo（Poppler 项目的一部分）渲染为 SVG 格式。这些项目的任何部分均不进行再分发。
- 网站：我们提供的所有 JavaScript 代码都是免费开源软件，其中大部分是我们自主开发的——您可以在我们的 GitHub 上找到它们。我们使用fast-fuzzy库来驱动搜索对话框，该库根据 ISC 许可证发布，许可证可在此处获取。

我们的内容均不依赖 JavaScript 运行，但启用 JavaScript 可以提升用户体验——您可以控制主题、使用搜索功能、浏览链接图、鼠标悬停时输入文字等等。如果您出于隐私考虑禁用了 JavaScript，请放心：1Lab 不会追踪您的活动，也不会收集任何个人身份信息。

## 其他资源

这是一份关于同伦类型理论的免费在线资源列表，它们不同的呈现方式（和公理体系）可能更符合某些读者的需求。欢迎查看！

- 前面提到的《同伦类型理论：数学的单价基础》（2013 年）一分为二，一部分介绍了同伦类型理论的实践，另一部分介绍了单价性在范畴论、同伦理论、集合论和实分析中的应用开端。
- Egbert Rijke 于2022 年出版的《同伦类型理论导论》是对依赖类型理论（尤其是同伦类型理论）实践的更全面的介绍。
- Martin Escardó 的《数学单价基础导论（Agda版）》运用定理证明器生成讲义，其结构与 1Lab 不同，是按顺序排列的。
- TypeTopology库主要由Escardó开发，但其主要功能是对构造性数学领域的新成果进行形式化。

## Mikan

Mikan 是 Agda 的一个分叉，专为支持 1Lab 项目而开发。源代码托管在 codeberg.org/1lab/mikan.git。通过 Cabal 安装：

```bash
cabal install Mikan -foptimise-heavily
```

系统环境已配置在 `/opt/mikan/`。

## 重点内容

### 类型理论
```agda
open import 1Lab.Type         -- 类型宇宙基础
open import 1Lab.Path         -- 立方类型理论的关键思想
open import 1Lab.HLevel       -- 同伦 n 类型的层次结构
open import 1Lab.Equiv        -- 等价性，类型的相同性概念
open import 1Lab.Univalence   -- 单价性的证明及其一些等价性
```

### 元编程
```agda
open import 1Lab.Reflection.HLevel
open import 1Lab.Extensionality
open import 1Lab.Reflection.Induction
open import 1Lab.Reflection.Induction.Examples
```

### 范畴论
```agda
open import Cat.Base                 -- 核心定义
open import Cat.Univalent            -- 单值范畴
open import Cat.Functor.Base         -- 函子范畴
open import Cat.Functor.Adjoint      -- 伴随函子
open import Cat.Functor.Equivalence  -- 范畴的等价性
```

### 双范畴论
```agda
open import Cat.Bi.Base
open import Cat.Bi.Instances.Spans
open import Cat.Bi.Diagram.Monad.Spans
```

### 笛卡尔封闭范畴
```agda
open import Cat.Diagram.Exponential
open import Cat.CartesianClosed.Free
open import Cat.CartesianClosed.Free.Lambda
```

### 常规类别
```agda
open import Cat.Regular
open import Cat.Bi.Instances.Relations
open import Cat.Allegory.Base
open import Cat.Allegory.Instances.Mat
open import Cat.Regular.Image
```

### 幺半范畴
```agda
open import Cat.Monoidal.Base
open import Cat.Monoidal.Instances.Day
open import Cat.Monoidal.Instances.Cartesian
```

### 内部范畴论
```agda
open import Cat.Internal.Base
```

### 显示的类别
```agda
open import Cat.Displayed.Base
open import Cat.Displayed.Univalence.Thin
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Cartesian.Indexing
open import Cat.Displayed.Comprehension
open import Cat.Displayed.Doctrine
open import Cat.Displayed.Instances.Slice
open import Cat.Displayed.Instances.Family
open import Cat.Displayed.Instances.Subobjects
open import Cat.Displayed.Instances.Externalisation
```

### 序理论
```agda
open import Order.Base
open import Order.Frame
open import Order.Lattice
```

### 领域理论
```agda
open import Order.DCPO
open import Order.DCPO.Free
open import Order.DCPO.Pointed
```

### 合成同伦理论
```agda
open import Homotopy.Base
open import Homotopy.Connectedness
open import Homotopy.Space.Circle
open import Homotopy.Space.Delooping
open import Homotopy.Space.Torus
open import Homotopy.Space.Sphere
open import Homotopy.Space.Sinfty
open import Homotopy.Space.Suspension
```

### 代数
```agda
open import Algebra.Monoid
open import Algebra.Group
open import Algebra.Ring
open import Algebra.Ring.Module
open import Algebra.Group.Free
open import Algebra.Group.Action
open import Algebra.Group.Cayley
open import Algebra.Group.Concrete
open import Algebra.Group.Ab
open import Algebra.Group.Ab.Tensor
open import Algebra.Group.Ab.Abelianisation
```

## 参考

- Borceux, Francis. 1994. 范畴代数手册。第 1 卷。数学及其应用百科全书。剑桥大学出版社。
- Cohen, Cyril, Thierry Coquand, Simon Huber 和 Anders Mörtberg. 2016. "立方类型理论：单值公理的构造性解释。" CoRR abs/1611.02108。
- Johnstone, Peter T. 2002. Sketches of an Elephant: a Topos Theory Compendium. Oxford Logic Guides.
- Rijke, Egbert. 2022. "同伦类型理论简介。" https://arxiv.org/abs/2212.11082。
- 单价基础计划，2013.《同伦类型理论：数学的单价基础》。普林斯顿高等研究院。
