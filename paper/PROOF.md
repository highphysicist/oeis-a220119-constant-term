# Proof of the constant-term conjecture in A220119

Contributor: Shreyas Samir Kolte. Substantial OpenAI ChatGPT/Codex assistance was used.

Working note, 23 November 2026.

The claim proved here is the **constant-term identity** proposed by
F. Chapoton on 25 May 2026 in [OEIS A220119](https://oeis.org/A220119).
The entry's separate divisibility conjecture is not proved here.

The accessible entry still labels this identity as conjectural. Targeted
searches did not locate an earlier proof, but this does not guarantee priority.
The proof below is an all-integer algebraic argument. The accompanying Lean formalization passed the recorded Lean 4.19.0
build and exact-statement/axiom audit. Independent human peer review is not claimed.

## Statement

Set

$$
F_n(k)=\binom nk^2\binom{n+k}{n},
\qquad
A_n=\sum_{j,k=0}^n F_n(j)F_n(k)\binom{j+k}{n}.
$$

Binomial coefficients with lower index negative or larger than the
nonnegative upper index are zero.

**Theorem.** For every integer \(n\geq0\),

$$
A_n=\operatorname{CT}_{a,b,c,d,e} P(a,b,c,d,e)^n,
$$

where

$$
P=
\frac{(1+c)(1+c+d)(1+a)(1+a+c+d+e)
(1+a+b)(1+a+b+c+d+e)}
{abcde}.
$$

Here CT means the coefficient of \(a^0b^0c^0d^0e^0\).
All computations take place in polynomial or Laurent-polynomial rings;
no analytic convergence assumptions are needed.

## 1. Auxiliary identity

For \(0\leq\ell\leq n\), define

$$
H_{n,\ell}=[c^nd^n](1+c)^n(1+c+d)^n(c+d)^\ell.
$$

We first prove

$$
\boxed{
\binom{2n-\ell}{n}H_{n,\ell}
=\sum_{k=0}^n F_n(k)\binom{k}{n-\ell}.
}
\tag{1}
$$

Put

$$
L_n(x)=\sum_{r=0}^n\binom nr\binom{n+r}{n}x^r.
$$

Expansion according to the total degree in \(c,d\) gives

$$
H_{n,\ell}
=\sum_{r=0}^{\ell}\binom nr\binom n{\ell-r}\binom{n+r}{n}
=[x^\ell](1+x)^nL_n(x).
\tag{2}
$$

Indeed, a term \(c^{n-r}\) from \((1+c)^n\) must be paired with
\((c+d)^{n+r}\); its coefficient of \(c^rd^n\) is
\(\binom{n+r}{n}\).

Vandermonde's identity proves the polynomial equality

$$
L_n(x)=\sum_{r=0}^n\binom nr^2x^r(1+x)^{n-r}.
\tag{3}
$$

Explicitly, the coefficient of \(x^t\) on the right is

$$
\sum_{r=0}^t\binom nr^2\binom{n-r}{t-r}
=\binom nt\sum_{r=0}^t\binom nr\binom tr
=\binom nt\binom{n+t}{n}.
$$

Equations (2)-(3) imply

$$
H_{n,\ell}=\sum_{r=0}^{\ell}\binom nr^2
\binom{2n-r}{\ell-r}.
\tag{4}
$$

For \(0\leq r\leq\ell\leq n\), factorial cancellation gives

$$
\binom{2n-\ell}{n}\binom nr^2\binom{2n-r}{\ell-r}
=\binom n\ell\binom nr\binom\ell r\binom{2n-r}{n}.
\tag{5}
$$

Both sides equal

$$
\frac{n!(2n-r)!}
{(r!)^2((n-r)!)^2(n-\ell)!(\ell-r)!}.
$$

Hence the left side of (1) is

$$
\binom n\ell\sum_{r=0}^{\ell}
\binom nr\binom\ell r\binom{2n-r}{n}.
\tag{6}
$$

For the right side, apply

$$
\binom nk\binom{k}{n-\ell}
=\binom n\ell\binom\ell{n-k},
$$

and substitute \(r=n-k\). This gives exactly (6), proving (1).

## 2. Extract the variables e and b

Let \(B_n=\operatorname{CT}P^n\), and write
\(X=1+a\), \(T=1+a+c+d=X+c+d\).
Then \(B_n\) is the coefficient of \(a^nb^nc^nd^ne^n\) in

$$
(1+c)^n(1+c+d)^n X^n(X+b)^n(T+e)^n(T+b+e)^n.
$$

The binomial theorem gives

$$
[e^n](T+e)^n(T+b+e)^n
=\sum_{i=0}^n\binom ni^2T^{n-i}(T+b)^i
$$

and

$$
[b^n](X+b)^n(T+b)^i
=
\sum_{\substack{0\leq j\leq n\\n-j\leq i}}
\binom nj\binom i{n-j}X^{n-j}T^{i-n+j}.
$$

After multiplication by \(X^nT^{n-i}\), the power of \(X,T\)
is \(X^{2n-j}T^j\). Its weight summed over \(i\) is

$$
\binom nj\sum_{i=0}^n\binom ni^2\binom i{n-j}
=\binom nj^2\binom{n+j}{n}=F_n(j).
\tag{7}
$$

To see (7), use
\(\binom ni\binom i{n-j}=\binom nj\binom j{n-i}\)
and Vandermonde.

Consequently,

$$
B_n=\sum_{j=0}^n F_n(j)R_{n,j},
$$

where

$$
R_{n,j}=[a^nc^nd^n](1+c)^n(1+c+d)^n
X^{2n-j}(X+c+d)^j.
$$

## 3. Finish by the auxiliary identity

Expand \((X+c+d)^j\) in powers of \(c+d\), then extract \(a^n\).
Since \([a^n]X^{2n-\ell}=\binom{2n-\ell}{n}\), this gives

$$
R_{n,j}=\sum_{\ell=0}^j
\binom j\ell\binom{2n-\ell}{n}H_{n,\ell}.
$$

Now apply (1) and Vandermonde:

$$
\begin{aligned}
R_{n,j}
&=\sum_{k=0}^n F_n(k)
  \sum_{\ell=0}^j\binom j\ell\binom{k}{n-\ell}\\
&=\sum_{k=0}^n F_n(k)\binom{j+k}{n}.
\end{aligned}
$$

Therefore

$$
B_n=\sum_{j,k=0}^nF_n(j)F_n(k)\binom{j+k}{n}=A_n.
$$

All sums are finite. Every formula remains valid at \(n=0\), so there
is no omitted initial case. This completes the proof.

## Checks and provenance

- The verification script independently expands the five-variable numerator,
  rather than computing a rearrangement of the target double sum.
- The saved run checks direct expansion for \(0\leq n\leq10\), and the
  intermediate identities for \(0\leq n\leq45\), using exact integers.
- These finite checks support error detection; the argument above proves
  the statement for all nonnegative integers.
- The defining double sum predates this note: see G. Almkvist and W. Zudilin,
  [Differential equations, mirror maps and zeta values](https://arxiv.org/abs/math/0402386),
  version 2 (2004), Section 4.
- The particular Laurent-polynomial conjecture is credited to F. Chapoton
  in OEIS, 25 May 2026.
- Publication and verification details are recorded in the repository README and evidence.
