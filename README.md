# ni-nbe
Noninterference by normalization (by evaluation)

This repo contains Agda mechanization of the proofs in the paper titled _Simple Proof of Noninterference by Normalization_ (currently under submission to PLAS 2019).

### About

Information-flow control (IFC) languages ensure programs
preserve the confidentiality of sensitive data. Noninterference,
the desired security property of such languages, states
that public outputs of programs must not depend on sensitive
inputs. We show that noninterference
can be proved using normalization. Unlike arbitrary terms,
normal forms of programs are well-principled and obey useful
syntactic properties—hence enabling a simpler proof of
noninterference. Since our proof is syntax-directed, it offers
an appealing alternative to traditional semantic based
techniques to prove noninterference.

In particular, we prove noninterference for a static IFC
calculus (based on the pure fragment of Haskell’s [seclib](http://hackage.haskell.org/package/seclib) library) 
using a normalization technique called _Normalization by Evaluation_ (NbE).

Pre-print coming soon!
