# What `verify_abc_bounds.py` proves

Repository: https://github.com/hanxinzhang/abc-exceptional-bound

The manuscript reduces its number-theoretic argument to seven finite claims:
for each listed anchor `Lambda`, every feasible point of a rational system of
inequalities satisfies `D <= r`.

The Python file checks those seven claims. It does **not** search for the
bounds and does not run an optimizer.

## The check in plain language

1. Reconstruct the manuscript's 22-variable finite system.
2. Choose one side of each of 13 initial two-way constraints, producing 8,192
   base branches.
3. Verify that permuting `a,b,c` reduces these to 1,632 representatives while
   still covering all 8,192 branches.
4. Follow the embedded proof tree for every representative. Each internal node
   makes another valid two-way split, so its children cover the parent.
5. At every leaf, read exact rational weights `y` and check

   ```text
   y >= 0,       A^T y >= e_D,       b^T y <= r,
   ```

   where that leaf's constraints are `A x <= b` and `x >= 0`. Consequently,

   ```text
   D = e_D^T x <= y^T A x <= y^T b <= r.
   ```

The long `COMPRESSED_PROOF_DATA` string is only a compact table of proof-tree
tags, subset masks, and rational numbers. It is not executable code. Every
decoded item is checked before the program can print `PASS`.

## Run

Python 3.9 or later; standard library only:

```bash
python3 -I -S verify_abc_bounds.py
```

A successful run ends with:

```text
ALL SEVEN UPPER BOUNDS VERIFIED
```

It checks 12,378 exact dual leaves, 954 valid geometry splits, and the complete
permutation reduction. It uses no floating point, optimizer, external data, or
third-party package. It proves the finite-program proposition only; the
analytic transfer to `N_lambda(X)` is the written argument in the manuscript.
