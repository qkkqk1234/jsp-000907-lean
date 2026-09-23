# Other Lean work — JSP-000907 / Erdős 1091

`plby/lean-proofs` (commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`) also contains a Lean
development of Erdős problem 1091. It has not been submitted to the Justin Sun Prize
repository by its owner.

The development in this repository does not depend on it and was written independently:
the Lean sources and the `tex` reconstruction in `plby/lean-proofs` were not read, and the
mathematics was taken from the published source, arXiv:2604.06609 §4. It uses its own
vertex encoding (a hub plus an indexed family of pentagon blocks) and its own proof of the
chord bound (a cut-parity argument).

The scope of this submission — the refutation of the second question of #1091, with chord
bound `30` — is set out in `STATEMENT.md`.
