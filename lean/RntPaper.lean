import RntPaper.Basic
import RntPaper.Endpoint
import RntPaper.InfiniteProduct
import RntPaper.SingleCrossing
import RntPaper.UniversalInequality
import RntPaper.Transport
import RntPaper.Extremal
import RntPaper.Ambient
import RntPaper.Consequences
import RntPaper.Lambda
import RntPaper.Stability
import RntPaper.MomentsSmall
import RntPaper.MomentsOdd
import RntPaper.Relative
import RntPaper.Moments1339
import RntPaper.K9Theorem

/-!
# Prime extremality for product integrals over primitive sets

Lean development for the paper (`../main.tex`). Section numbers in docstrings refer
to the paper. There are no `sorry`s. This root imports everything that does not need
PrimeNumberTheoremAnd; the PNT-dependent modules (`PNT`, `TailSecond`) are built
separately (see `README.md`). `MomentsOdd`, `Relative`, `Moments1339` and `K9Theorem` formalize
the follow-up results of `../supplement/discovery/notes.tex` (Theorems 3.2, 3.5, 3.7, 3.8).
-/
