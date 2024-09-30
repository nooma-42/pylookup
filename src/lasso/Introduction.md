To generate a lookup argument for large table, many works need to commit the whole table, which requires large polynomial commitment. Lasso uses several techniques to handle the large table with only small commitment.

## Problem definition and notations

The prover and the verifier know a public table $t \in \mathbb{F}^n$. The prover has a private $a \in \mathbb{F}^m$  and wants to generate a zero-knowledge argument to prove that $a[i] \in t, \forall i \in [m]$. To do so, the prover can show that it knows $M \in \mathbb{F}^{m \times n}$ where each row of $M$ has one cell of value $1$ and the rest are $0$, such that

$$
M \cdot t = a
$$

### Multilinear extension polynomial

Given a list $f$ where $|f|=2^\ell$, we can naturally convert any $x < 2^\ell$ into $(x_1, \ldots, x_\ell) \in \{0, 1\}^\ell, \forall x \in [2^\ell]$ and define a boolean hypercube $f: \{0,1\}^\ell \to \mathbb{F}$, $f(x_1, \ldots, x_\ell) = f[x]$.

The polynomial $\tilde{f}: \mathbb{F}^\ell \to \mathbb{F}$ is called the multilinear extension polynomial (MLE) of $f$ if

- $\tilde{f}(x_1, \ldots, x_\ell) = f(x_1, \ldots, x_\ell)$ for each $x_i \in \{0, 1\}$,
- each variable of $\tilde{f}$ has at most degree $1$. 

$\tilde{f}$ can be constructed as follows:

$$
f(x_1, \ldots, x_\ell) = \sum_{w \in \{0,1\}^\ell} f(w) \cdot \chi_w(x_1, \ldots, x_\ell)
$$

where $\chi_w(x_1, \ldots, x_\ell) = \prod_{i=1}^\ell (x_i w_i + (1-x_i)(1-w_i))$. It’s easy to check that $\forall x, w \in \{0, 1\}^\ell$, $\chi_w(x)$ outputs $1$ when $x=w$, otherwise outputs $0$.

To prove that $M \cdot t = a$, it is equivalent to prove the MLE version: for random $r \in \mathbb{F}^m$ chosen by the verifier, the prover proves that

$$
\sum_{y \in \{0, 1\}^{\log N}} \tilde{M}(r, y) \cdot \tilde{t}(y) = \tilde{a}(r)
$$

## Multivariate KZG polynomial commitment

Lasso can make use of any multilinear polynomial commitment scheme. Here we use a multivariate KZG commitment scheme [PST13].

Recall that in original (single variate) KZG, the idea is that we can find $q(x)$ such that $f(x) - f(a) = (x-a) \cdot q(x)$. Now let’s consider multivariate polynomials. Let $f$ be a $\ell$-variate polynomial. First, we can find $q_1(x_1, \ldots, x_n)$ such that

$$
f(x_1, \ldots, x_\ell) - f(a_1, x_2, \ldots, x_\ell) = (x_1 - a_1) \cdot q_1(x_1, \ldots, x_n)
$$

Similarly, we can find $q_2(x_2, \ldots, x_n)$ such that $f(a_1, x_2, \ldots, x_\ell) - f(a_1, a_2, x_3, \ldots, x_\ell) = (x_2-a_2) \cdot q_2(x_2, \ldots, x_n)$, and so on. Finally, we can get

$$
f(x)-f(a) = \sum_{i=1}^\ell (x_i - a_i) \cdot q_i(x)
$$

Let $\zeta = (\zeta_1, \ldots, \zeta_\ell)$ be a random point from common reference string. The commitment of $f$ is $comm = g_1^{f(\zeta)}$. The evaluation proof of $v=f(a)$ is $\{w_i\}_{i=1}^\ell$ where $w_i=g_1^{q_i(\zeta)}$. To check the evaluation proof, the verifier checks that

$$
e(comm \cdot g_1^{-v}, g_2) = \prod_{i=1}^\ell e(w_i, g_2^{\zeta_i - a_i})
$$

### Setup

The prover needs to compute $g_1^{f(\zeta)}$. Let the maximum degree of $x_i$ in $f$ is $s_i$, we need to generate $g_1^{\zeta_1^{d_1} \zeta_2^{d_2} \cdots \zeta_\ell^{d_\ell}}, \forall 0 \le d_i \le s_i$. In our case where $f$ is a multilinear polynomial, we need to compute for all $(d_1, \ldots, d_\ell) \in \{0, 1\}^\ell$, which has $2^\ell$ terms. Besides, we also need to generate $g_2^{\zeta_1}, \ldots, g_2^{\zeta_\ell}$.

## Sparse polynomial and SOS table

For lookup table applications, $m$ is usually small but $n$ could be very large such as $2^{128}$. Therefore, the polynomial $\tilde{M}$ would be very sparse. Follow Spartan [SET20], we can represent $\tilde{M}$ in a more efficient way:

First we add the index to each entry of the table $t$. To represent $M$, we only need the index of $t$ for each element in $a$. More specifically, let $a[i] = t[idx_i], \forall i \in [m]$, we can represent $M$ by $[(1, idx_1), \ldots, (m, idx_m)]$. As for the MLE form, we have

$$
\tilde{M}(r, y) = \sum_{i=1}^m \chi_i(r) \cdot \chi_{idx_i}(y)
$$

So the problem becomes to prove that

$$
\sum_{y \in \{0, 1\}^{\log N}} \sum_{i=1}^m \chi_i(r) \cdot \chi_{idx_i}(y) \cdot \tilde{t}(y) = \tilde{a}(r)$$

Note that $\chi_{idx}$ and $t$ have $\log{n}$ variables. Lasso makes the polynomials with less variable to speed up polynomial operations and commitments. Let $\ell \ge \log {m}$, we want to replace $\chi_{idx_i}$ and $\tilde{t}$ with several $\ell$-variate multilinear polynomials.

In fact, not every table allows us to find the replacement. Lasso requires the table $t$ to be *Spark-only structured* (SOS).

### SOS table

Before we dive into the definition of SOS table, let's consider a simple but useful case. Consider that the prover wants to prove that some numbers are between $[1, n]$, so the table is simply $[1, 2, \ldots, n]$. 

Let $c = \lceil \frac{\log{n}}{\ell} \rceil$. Given an index $idx = (idx^{(1)}, \ldots, idx^{(c)}) \in (\{0, 1\}^\ell)^c$, we have $t[idx] = 1 + idx = 1 + idx^{(1)} + idx^{(2)} \cdot 2^\ell + \ldots + idx^{(c)} \cdot 2^{\ell(c-1)}$. Therefore, we can use $c$ subtables $t_1, \ldots, t_c, \forall (i, idx): t_i[idx] = idx$ and define a multilinear polynomial $g(x_1, \ldots, x_\ell) = 1 + x_1 + x_2 \cdot 2^\ell + \ldots + x_c \cdot 2^{\ell(c-1)}$ such that $g(t_1[idx^{(1)}], \ldots, t_c[idx^{(c)}]) = t[idx]$.

Let $E_j$ be the MLE of the list $(t_j[idx_1^{(j)}], \ldots, t_j[idx_m^{(j)}])$, we have

$$
\sum_{y \in \{0, 1\}^{\log N}} \sum_{i=1}^m \chi_i(r) \cdot \chi_{idx_i}(y) \cdot \tilde{t}(y) = \sum_{i=1}^m \chi_i(r) \sum_{y \in \{0, 1\}^{\log N}} \chi_{idx_i}(y) \cdot \tilde{t}(y) = \sum_{i=1}^m \chi_i(r) \cdot \tilde{t}(idx_i)
$$

$$
= \sum_{i=1}^m \chi_i(r) \cdot g(E_1(i), \ldots, E_c(i)) = \sum_{i \in \{0, 1\}^{\log{m}}} \chi_r(i) \cdot g(E_1(i), \ldots, E_c(i))
$$

So it becomes to prove that $\tilde{a}(r) = \sum_{i \in \{0, 1\}^{\log{m}}} \chi_r(i) \cdot g(E_1(i), \ldots, E_\ell(i))$. 

Now we introduce the SOS table. Table $t$ is SOS means that there is an integer $k$ and $\alpha = k \cdot c$ subtables $t_1, \ldots, t_\alpha$ of size $2^\ell$, and an $\alpha$-variate multilinear polynomial $g$ such that

$$
t[idx] = g(t_1[idx^{(1)}], \ldots, t_k[idx^{(1)}], t_{k+1}[idx^{(2)}], \ldots, t_{2k}[idx^{(2)}], \ldots, t_{\alpha-k+1}[idx^{(c)}], \ldots, t_\alpha[idx^{(c)}])
$$

We can see that the above example is a special case for $k=1$. For the SOS table, similarly, the prover generates $E_1, \ldots, E_\alpha$ and proves that

$$
\tilde{a}(r) = \sum_{i \in \{0, 1\}^{\log{m}}} \chi_r(i) \cdot g(E_1(i), \ldots, E_\alpha(i))
$$

to the verifier. Then the prover and the verifier perform the following steps:

- The prover commits $a, E_1, \ldots, E_\alpha$.
- The prover and the verifier run a **sumcheck protocol** to prove that $\tilde{a}(r) = \sum_{i \in \{0, 1\}^{\log{m}}} \chi_r(i) \cdot g(E_1(i), \ldots, E_\alpha(i))$.
- The prover commits $dim_1, \ldots, dim_c$, where $dim_i$ is the MLE of $(idx^{(i)}_1, \ldots, idx^{(i)}_m)$.
- For each subtable $E_j$, the prover uses **offline memory checking** to prove the correctness of the memory access.

Note that all the subtables $t_1, \ldots, t_\alpha$ and polynomial $g$ are public.

## Sumcheck protocol

Given a $\ell$-variate polynomial $f$, the prover wants to prove that $k = \sum_{i \in \{0, 1\}^\ell} f(i)$ to the verifier. They run a $\ell$-round protocol where the $j^{th}$ round does the follows:

- The prover computes a single variate polynomial $f_j(x) = \sum_{i = \{0, 1\}^{\ell-j}} f(r_1, \ldots, r_{j-1}, x, i_1, \ldots, i_{\ell-j})$ and send it to the verifier.
- The verifier checks that $f_j(0) + f_j(1) = k_{j-1}$ (define $k_0 = k$).
- The verifier chooses $r_j \in \mathbb{F}$ and computes $k_j = f_j(r_j)$, and sends $r_j$ to the prover.

After the sumcheck protocol, both of the prover and the verifier get $r' = (r_1, \ldots. r_\ell)$ and $f(r')$. $f(r')$ can be used for further checking. In our case, the prover and the verifier run the sumcheck protocol on polynomial $h(x) = \chi_r(x) \cdot g(E_1(x), \ldots, E_\alpha(x))$. The prover then provides $E_1(r'), \ldots, E_\alpha(r')$ and their evaluation proofs. The verifier can check the proofs and that $h(r') = \chi_r(r') \cdot g(E_1(r'), \ldots, E_\alpha(r'))$.

## Offline memory checking

Offline memory checking [BEG+91] uses "Memory-in-the-head" technique: it commits the "memory checking process" of the table $t$ and solve the challenge from the verifier later.

[This Mandarin article](https://github.com/sec-bit/learning-zkp/blob/develop/lookup-arguments/lasso-zh/lasso-1.md) describes memory checking very well, so we simply fetch part of the article and translate it into English. The "memory checking process" can be considered as the transformation between the states $S_0 \overset{T_1}{\to} S_1 \overset{T_2}{\to} S_2 \overset{T_3}{\to} \cdots \overset{T_m}{\to} S_m$ where each $T_i$ is a memory operation and $S_0$ is the initial state as follows:

$$
S_0 = \begin{array}{c|c|c}
\text{index} & \text{value} & \text{counter} \\
\hline
0 & t_0 & 0 \\
1 & t_1 & 0 \\
2 & t_2 & 0 \\
\vdots & \vdots & \vdots \\
2^\ell-1 & t_{2^\ell-1} & 0 \\
\end{array}
$$

Each operation $T_i$ does the follows:

- read index $j = idx_i$ and log $R_i = (j, t_j, ctr)$
- add $1$ to the counter of index $j$ (change the state)
- log $W_i = (j, t_j, ctr+1)$

For example, we may have the following log and state transformation:

$$
S_0: \begin{bmatrix}
0, & t_0, & 0 \\
1, & t_1, & 0 \\
2, & t_2, & 0 \\
3, & t_3, & 0 \\
\end{bmatrix} 
\xrightarrow[W_1 = (1, t_1, 1)]{R_1 = (1, t_1, 0)}
S_1: \begin{bmatrix}
0, & t_0, & 0 \\
1, & t_1, & {\color{red}1} \\
2, & t_2, & 0 \\
3, & t_3, & 0 \\
\end{bmatrix}
\xrightarrow[W_2 = (3, t_3, 1)]{R_2 = (3, t_3, 0)}
S_2: \begin{bmatrix}
0, & t_0, & 0 \\
1, & t_1, & 1 \\
2, & t_2, & 0 \\
3, & t_3, & {\color{red}1} \\
\end{bmatrix}
\xrightarrow[W_3 = (1, t_1, 2)]{R_3 = (1, t_1, 1)}
S_3 : \begin{bmatrix}
0, & t_0, & 0 \\
1, & t_1, & {\color{red}2} \\
2, & t_2, & 0 \\
3, & t_3, & 1 \\
\end{bmatrix}
$$

To prove the correctness of memory checking, the prover only need to show the multiset equality:

$$
S_0 \cup \{W_i\} = S_m \cup \{R_i\}
$$

Follow Plonk’s idea, the verifier provides random challenge $\tau, \gamma \in \mathbb{F}$, and the prover shows that

$$
\prod_{s \in S_0} H_{\tau, \gamma}(s) \cdot \prod_{i=1}^m H_{\tau, \gamma}(W_i) = \prod_{s \in S_m} H_{\tau, \gamma}(s) \cdot \prod_{i=1}^m H_{\tau, \gamma}(R_i)
$$

where $H$ is the hash function for tuple $s = (i, v, c): H_{\tau, \gamma}(s) = i \cdot \tau^2 + v \cdot \tau + c - \gamma$.

Plonk’s grand product protocol is only suitable for single variate polynomial. As for multivariate polynomial, lasso uses sumcheck-based grand product protocol [SL20, Section 5]. First, the prover commits the following MLEs (follow Lasso's notation):

- $read$ ($\log{m}$-variate): MLE of the counters $(R_1.ctr, \ldots, R_m.ctr)$
- $final$ ($\ell$-variate): MLE of the counters $(S_m.ctr)$

For the 4 grand products $\prod_{s \in S_0} H_{\tau, \gamma}(s), \prod_{i=1}^m H_{\tau, \gamma}(W_i), \prod_{s \in S_m} H_{\tau, \gamma}(s), \prod_{i=1}^m H_{\tau, \gamma}(R_i)$, the prover and the verifier run the following protocol:

### Sumcheck-based grand product protocol

Given a $\ell$-dimension boolean hypercube $v$, the prover wants to prove that $P = \prod_{x\ \in \{0, 1\}^\ell} v(x)$. First, the prover generates a $\ell+1$-dimension hypercube $f$ where $\forall x \in \{0, 1\}^\ell$, 

- $f(0, x) = v(x)$
- $f(1, x) = f(x, 0) \cdot f(x, 1)$ ($x \ne 1^\ell$)
- $f(1^{\ell+1}) = 0$ to satisfy that $f(1, x) = f(x, 0) \cdot f(x, 1)$ when $x = 1^\ell$

It’s easy to verify that $f(1, \ldots, 1, 0) = \prod_{x \in \{0, 1\}^\ell} v(x) = P$.

Next, the prover commits $\tilde{f}$, the MLE of $f$. Then the prover and the verifier run the sumcheck protocol on $g(x) = \chi_r(x) \cdot (\tilde{f}(1, x) - \tilde{f}(x, 0) \cdot \tilde{f}(x, 1))$ to prove that
$0 = \sum_{x \in \{0, 1\}^\ell} g(x)$, where $r$ is a random element in $\mathbb{F}^\ell$. The verifier also gets $g(r')$ for some $r’ \in \mathbb{F}^\ell$ in the sumcheck protocol.

At last, the prover provides the evaluation and proof of $\tilde{f}(0, r'), \tilde{f}(1, r'), \tilde{f}(r', 0), \tilde{f}(r', 1)$ and $\tilde{f}(1, \ldots, 1, 0)$. The verifier verify the evaluation proofs and check that $g(r’) = \chi_r(r’) \cdot (\tilde{f}(1, r’) - \tilde{f}(r’, 0) \cdot \tilde{f}(r’, 1))$. If all the check are passed, the verifier get $\tilde{f}(1, \ldots, 1, 0) = \prod_{x\ \in \{0, 1\}^\ell} v(x)$ as the grand product and $\tilde{f}(0, r’) = \tilde{v}(r’)$ for the following checking.

### Back to offline memory checking

The verifier gets $\tilde{S_0}(r'), \tilde{S}(r''), \tilde{RS}(r'''), \tilde{WS}(r'''')$ from the grand product protocol. Then it can make use of these values to check $dim,read,final$. For example:

- $\tilde{RS}(r''')=H_{\tau,\gamma}(dim(r'''),E(r'''),read(r'''))$
- $\tilde{S}(r'') = H_{\tau, \gamma}(\tilde{idx}(r''), \tilde{t}(r''), final(r''))$

where $\tilde{idx}$ is the MLE of $(0, 1, \ldots, L-1)$ and $\tilde{t}$ is the MLE of the subtable, both of which can be computed by the verifier. So the prover remains to provide $dim(r'''), E(r'''), read(r'''), final(r'')$ and the evaluation proof to the verifier.

## The whole protocol

### Setup

- Publish the subtables and the $g$ function.
- Run the multivariate KZG setup for multilinear polynomial.

### Round 1

- The prover commits $\tilde{a}$ and $dim_1, \ldots, dim_c$.
- The verifier chooses $r \in \mathbb{F}^{\log{m}}$.

### Round 2

- The prover provides $\tilde{a}(r)$ and the evaluation proof.
- For each subtable, the prover
    - commits $E$,
    - runs the offline memory checking and commits $read, final$.
- The verifier checks the evaluation proof of $\tilde{a}(r)$.

### Round 3

- The prover and the verifier run the sumcheck protocol on $h(x) = \chi_r(x) \cdot g(E_1(x), \ldots, E_\alpha(x))$
- The prover provides $E_1(r'), \ldots, E_\alpha(r')$ and their evaluation proofs.
- The verifier checks that $\tilde{a}(r) = \sum_{i \in \{0, 1\}^{\log{m}}} h(i)$ and $h(r') = \chi_r(r') \cdot g(E_1(r'), \ldots, E_\alpha(r'))$.

### Round 4

- For each subtable,
    - the prover and the verifier run the sumcheck-based grand product protocol on each $S_0, WS, S, RS$,
    - the verifier checks that $\tilde{S_0}(1, \ldots, 1, 0) \cdot \tilde{WS}(1, \ldots, 1, 0) = \tilde{S}(1, \ldots, 1, 0) \cdot \tilde{RS}(1, \ldots, 1, 0)$.

### Round 5

- For each subtable,
    - the prover provides $dim(r'''), E(r'''), read(r'''), final(r'')$ and their evaluation proofs,
    - the verifier checks that $\tilde{RS}(r''')=H_{\tau,\gamma}(dim(r'''),E(r'''),read(r'''))$ and $\tilde{S}(r'') = H_{\tau, \gamma}(\tilde{idx}(r''), \tilde{t}(r''), final(r''))$.

## Reference

1. Lasso: [https://eprint.iacr.org/2023/1216.pdf](https://eprint.iacr.org/2023/1216.pdf)
2. Spartan [SET20]: [https://eprint.iacr.org/2019/550.pdf](https://eprint.iacr.org/2019/550.pdf)
3. Multivariate KZG [PST13]: [https://eprint.iacr.org/2011/587.pdf](https://eprint.iacr.org/2011/587.pdf)
4. Sumcheck protocol [LFNK90]: [https://dl.acm.org/doi/pdf/10.1145/146585.146605](https://dl.acm.org/doi/pdf/10.1145/146585.146605)
5. Offline memory checking [BEG+91]: [https://citeseerx.ist.psu.edu/document?repid=rep1&type=pdf&doi=f6a5b92dd68297f9ac328b01d2507c93e377efa9](https://citeseerx.ist.psu.edu/document?repid=rep1&type=pdf&doi=f6a5b92dd68297f9ac328b01d2507c93e377efa9)
6. Memory checking explanation (Mandarin): [https://github.com/sec-bit/learning-zkp/blob/develop/lookup-arguments/lasso-zh/lasso-1.md](https://github.com/sec-bit/learning-zkp/blob/develop/lookup-arguments/lasso-zh/lasso-1.md)
7. Sumcheck-based grand product protocol [SL20, Section 5]: [https://eprint.iacr.org/2020/1275.pdf](https://eprint.iacr.org/2020/1275.pdf)