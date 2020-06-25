# ni-nbe
Noninterference by normalization (by evaluation)

This repository contains the Agda mechanization of the proofs in the paper titled _Simple Proof of Noninterference by Normalization_ [PLAS'19].

[PLAS'19] Carlos Tomé Cortiñas and Nachiappan Valliappan, PLAS'19: Proceedings of the 14th ACM SIGSAC Workshop on Programming Languages and Analysis for Security, https://doi.org/10.1145/3338504.3357342

### About

Information-flow control (IFC) languages ensure programs preserve the
confidentiality of sensitive data. Noninterference, the desired security
property of such languages, states that public outputs of programs must not
depend on sensitive inputs. We show that noninterference can be proved using
normalization. Unlike arbitrary terms, normal forms of programs are
well-principled and obey useful syntactic properties—hence enabling a simpler
proof of noninterference. Since our proof is syntax-directed, it offers an
appealing alternative to traditional semantic based techniques to prove
noninterference.

In particular, we prove noninterference for a static IFC calculus (based on the
pure fragment of Haskell’s [seclib](http://hackage.haskell.org/package/seclib)
library) using a normalization technique called _Normalization by Evaluation_
(NbE).

### Agda requirements

The code type checks using Agda version 2.6.1 and agda standard library version 1.3
