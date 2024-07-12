# RingSQISign-SageMath

A SageMath implementation of some additional function related to SQISign, starting from a fork of [LearningToSQI/SQISign-SageMath](https://github.com/LearningToSQI/SQISign-SageMath).
For now it contains:
1. Some additional basic functionalities, like `isogeny_to_ideal`. 
2. A distinguisher that is capable of understanding if an ideal has been generated by SigningKLPT or not, given the connecting ideal used for the procedure. Example of the use on a response isogeny `sigma` and a secret key `Iτ`:

```python
sage: from deuring import isogeny_to_ideal
sage: J = isogeny_to_ideal()
sage: from attack import distinguisher
sage: distinguisher(JJ, Iτ)
```
3. Two variants of the SQIsign identification protocol, from XXX. The first one consider a chllenge isogeny starting from the public curve, the other achieving 
***strong** Honest Verifier Zero Knowledge* 
thanks to an additional randomization step.
4. A linear size Ring Signature based on SQISign called *Erebor*, with two version, a shorter one and a *full-anonymous* one from XXX.

## Project Overview

As for the initial project SQISign itself is implemented in the file [`SQISign.py`](SQISign.py).

If you wish to run SQISign and test the disringuisher you can execute [`example_SQISign.sage`](example_SQISign.sage) and then try random ideals vs KLPT ideals.

**Remark**: for now the script is super slow because of `isogeny_to_ideal`, we plan to improve it.




### References

- [SQISign: compact post-quantum signatures from quaternions and isogenies](https://eprint.iacr.org/2020/1240), Luca De Feo, David Kohel, Antonin Leroux, Christophe Petit, and Benjamin Wesolowski (2020).
- [New algorithms for the Deuring correspondence: toward practical and secure SQISign signatures](https://eprint.iacr.org/2022/234), Luca De Feo, Antonin Leroux, Patrick Longa and Benjamin Wesolowski (2022).
- [Quaternion algebras and isogeny-based cryptography](https://www.lix.polytechnique.fr/Labo/Antonin.LEROUX/manuscrit_these.pdf), Antonin Leroux (PhD Thesis) (2022).
- [On the quaternion $\ell$-isogeny path problem](https://arxiv.org/abs/1406.0981), David Kohel, Kristin Lauter, Christophe Petit, Jean-Pierre Tignol (2014).
- [Supersingular isogeny graphs and endomorphism rings: reductions and solutions](https://eprint.iacr.org/2018/371), Kirsten Eisenträger, Sean Hallgren, Kristin Lauter, Travis Morrison Christophe Petit (2018).
- [An improvement to the quaternion analogue of the l-isogeny path problem](https://crypto.iacr.org/2018/affevents/mathcrypt/page.html), Christophe Petit and Spike Smith (2018).
- [Deuring for the People: Supersingular Elliptic Curves with Prescribed Endomorphism Ring in General Characteristic](https://ia.cr/2023/106) Jonathan Komada Eriksen, Lorenz Panny, Jana Sotáková, and Mattia Veroni (2023).
- [SQIsign2D-West: The Fast, the Small, and the Safer](https://eprint.iacr.org/2024/760) Andrea Basso, Luca De Feo, Pierrick Dartois, Antonin Leroux, Luciano Maino, Giacomo Pope, Damien Robert, Benjamin Wesolowski (2024).
