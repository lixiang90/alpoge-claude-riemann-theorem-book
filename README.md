# Alpöge-Claude-Riemann Theorem

本仓库收录两本同名英文书，分别由 GPT-6.2 Astra 和 Gemini 4 Neon 撰写。两书讲解 Levent Alpöge 于 2026 年 11 月 20 日公布的、与 Claude 合作完成的 Lean 证明，涵盖黎曼猜想及其对狄利克雷 $L$ 函数的推广。

This repository contains two English-language books under the same title, one by GPT-6.2 Astra and one by Gemini 4 Neon. On 20 November 2026, Levent Alpöge announced a Lean proof developed with Claude. Both books explain how the proof treats the Riemann hypothesis and its generalization to Dirichlet $L$-functions.

| 书稿 / Book | 页数 / Pages | PDF | Typst 主文件 / Entry point |
| --- | ---: | --- | --- |
| [GPT-6.2 Astra](book-gpt6.2/) | 291 | [下载修订版 / Download v1.0.1](https://github.com/lixiang90/alpoge-claude-riemann-theorem-book/releases/download/v1.0.1/Alpoge-Claude-Riemann-Theorem-Revised.pdf) · [仓库副本 / Repository PDF](book-gpt6.2/pdf/Alpoge-Claude-Riemann-Theorem-Revised.pdf) | [volume.typ](book-gpt6.2/typst/volume.typ) |
| [Gemini 4 Neon](book-gemini4/) | 595 | [下载 / Download](book-gemini4/pdf/Alpoge-Claude-Riemann-Theorem.pdf?raw=1) | [main.typ](book-gemini4/typst/main.typ) |

[GPT-6.2 Astra v1.0.1 发布说明与 SHA-256 校验值 / Release notes and SHA-256 checksum](https://github.com/lixiang90/alpoge-claude-riemann-theorem-book/releases/tag/v1.0.1)

## 中文

**GPT-6.2 Astra 修订版**以素数计数的误差为主线。为什么一个复函数的零点能控制这个误差？全书 18 章，从黎曼 1859 年的论文讲到梅林变换和狄利克雷特征，再追踪一个假想的偏线零点如何迫使加权素数和越过算术上界。书中有 25 道附解答的习题，附录 C 对照了数学命题、mathlib 定义和独立核验记录。

**Gemini 4 Neon 版**分四部分、18 章。它用有限域上的 Stepanov 方法引出重数在证明中的作用，随后讲解酉群上的西塔提升和 Bost 斜率不等式，最后回到 Lean 4 形式化。附录 A 按证明步骤列出 Lean 模块，附录 B 汇集渐近参数和主要不等式。

## English

**The GPT-6.2 Astra revised edition** asks how a zero of a complex function can govern the error in counting primes. Its 18 chapters lead from Riemann’s 1859 paper through Mellin transforms and Dirichlet characters, then follow a hypothetical zero off the critical line to a weighted prime sum that would exceed its arithmetic bound. The book includes 25 problems with solutions. Appendix C compares the mathematical statements with their mathlib definitions and the independent verification record.

**The Gemini 4 Neon edition** has four parts and 18 chapters. It uses Stepanov’s method over finite fields to introduce the role of multiplicity, then develops theta lifts on unitary groups and Bost’s slope inequality before turning to the Lean 4 formalization. Appendix A maps the steps of the proof to Lean modules. Appendix B collects the asymptotic parameters and main inequalities.

## 源码与编译 / Source and build

在仓库根目录用 Typst 0.14.0 运行对应的命令。GPT-6.2 版使用 Arial，Gemini 4 版使用 DejaVu Sans Mono 排版代码。

Run the command for your chosen book from the repository root with Typst 0.14.0. The GPT-6.2 edition uses Arial, and the Gemini 4 edition uses DejaVu Sans Mono for code.

```sh
typst compile --root book-gpt6.2/typst book-gpt6.2/typst/volume.typ gpt6.2-book.pdf
typst compile --root book-gemini4/typst book-gemini4/typst/main.typ gemini4-book.pdf
```

## 原始资料 / Primary sources

- [Alpöge 的公布说明 / Alpöge’s announcement](https://alpo.ge/remark.pdf)
- [Lean 证明的固定版本 / Pinned Lean proof](https://github.com/leanprover-community/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005)
- [Andrew Sutherland 的独立验证记录 / Andrew Sutherland’s verification record](https://math.mit.edu/~drew/grh/)
