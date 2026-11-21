# Alpöge-Claude-Riemann Theorem

[下载修订版 PDF · Download the revised PDF](https://github.com/lixiang90/alpoge-claude-riemann-theorem-book/releases/download/v1.0.1/Alpoge-Claude-Riemann-Theorem-Revised.pdf) · [GitHub Release v1.0.1](https://github.com/lixiang90/alpoge-claude-riemann-theorem-book/releases/tag/v1.0.1)

## 中文

为什么一个复函数的零点能决定素数计数的误差？本书从黎曼 1859 年提出的问题讲起，回顾临界线上零点的研究历史，再介绍梅林变换、狄利克雷特征、格与伽罗瓦上同调。后半部分沿着一个假想的偏线零点展开，说明它会怎样迫使一个素数和越过上界，以及算术估计怎样排除这种可能。

本书由 GPT-6.2 Astra 用英文撰写，讲解 Levent Alpöge 于 2026 年 11 月 20 日公布的、与 Claude 合作完成的 Lean 证明，涵盖普通黎曼猜想和狄利克雷 $L$ 函数的相应结论。修订版共 291 页、18 章，含 25 道附解答的习题。附录 C 对照了数学命题、mathlib 定义和独立核验记录。

## English

How can a zero of a complex function govern the error in counting primes? The book begins with Riemann’s 1859 question and the history of zeros on the critical line. It develops the Mellin transform, Dirichlet characters, lattices, and Galois cohomology. The second half follows one hypothetical zero off the line, showing how it would force a weighted prime sum above a bound that arithmetic supplies.

Written in English by GPT-6.2 Astra, this book gives an expository account of the Lean proof that Levent Alpöge announced on 20 November 2026 following his work with Claude. It covers the ordinary Riemann hypothesis and the corresponding results for Dirichlet $L$-functions. The revised edition has 291 pages, 18 chapters, and 25 problems with solutions. Appendix C compares the mathematical statements with their mathlib definitions and the independent verification record.

## 源码与编译 / Source and build

[Typst 主文件 / Typst entry point](typst/volume.typ) · [仓库中的 PDF / PDF in the repository](pdf/Alpoge-Claude-Riemann-Theorem-Revised.pdf)

在仓库根目录用 Typst 0.14.0 编译。发布版使用 Arial 以及 Typst 随附的字体。  
From the repository root, compile with Typst 0.14.0. The published edition uses Arial alongside Typst’s bundled fonts.

```sh
typst compile --root typst typst/volume.typ book.pdf
```

## 原始资料 / Primary sources

- [Alpöge 的公布说明 / Alpöge’s announcement](https://alpo.ge/remark.pdf)
- [Lean 证明的固定版本 / Pinned Lean proof](https://github.com/leanprover-community/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005)
- [Andrew Sutherland 的独立验证记录 / Andrew Sutherland’s verification record](https://math.mit.edu/~drew/grh/)
