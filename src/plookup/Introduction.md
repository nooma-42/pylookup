# Plookup Introduction

Plookup is a Plonk-based lookup argument. In this article, we start from Plonk's techniques and show that how Plookup applies the techniques to the lookup argument.

## Plonk's proof of multiset equality

In the permutation argument of Plonk, they perform the multiset equality proof as follows:

The prover has two multisets $s$ and $t$, and it wants to prove to the verifier that $s$ and $t$ are the same multiset. To do so, the verifier provide a random $\gamma \in \mathbb{F}$, and the prover proves that:

$\prod_{i=1}^n (s_i + \gamma) = \prod_{i=1}^n (t_i + \gamma)$

## Prove lookup from multiset equality

How do we use the multiset equality to prove lookup? That is, given a witness $f$ and table $t$, we want to prove that $f_i \in t, \forall i \le |f|$. 

- Note: Plookup requires that $|f| = |t| - 1$ (denote this number as $n$), so when $|f| < |t| - 1$, we need to pad $|f|$ to length $|t|-1$. For example, given $t = [1,2,3,4,5,6,7,8]$ and $f = [4,8,7,6,3]$, we need to pad $f$ to length $7$. We achieve this by simply repeating the last element, i.e., $f = [4,8,7,6,3,3,3]$.

The protocol doesn't specifically explain the reason for this requirement.

First, we construct an array $s$, which is the sorted array of $f+t$ based on the order of $t$. For example, given $t = [1,2,3,4,5,6,7,8]$ and $f = [4,8,7,6,3,3,3]$, we have $s = [1,2,3,3,3,3,4,4,5,6,6,7,7,8,8]$. So $|s| = |f| + |t| = 2n+1$.

The original Plookup paper states that they focus on the non-zero difference of each multiset. But I think that [this article](https://github.com/sec-bit/learning-zkp/blob/develop/plonk-intro-cn/7-plonk-lookup.md) has better insight, so our description follows that article. The prover proves the equality of these two multisets:

- $\{(f_i, f_i)\} + \{(t_i, t_{i+1})\}$
- $\{(s_i, s_{i+1})\}$

Simply comparing whether the element sets of $s$ and $f$, $t$ are equal is not sufficient. For example, $t = \{1, 4, 8\}$ and $f = \{5, 5\}$. After merging and sorting, $s = \{1, 4, 5, 5, 8\}$. If we only look at the element sets, $\{1, 4, 5, 5, 8\}$ seems to include both $\{5, 5\}$ and $\{1, 4, 8\}$. But $5$ in $f$ is not in $t$.

Plookup solves this problem by comparing transition pairs:
The transition pairs in $s$ are $\{(1,4), (4,5), (5,5), (5,8)\}$.
The valid transition pairs formed by $f$ and $t$ are $\{(5,5)\} + \{(1,4), (4,8)\} = \{(1,4), (4,8), (5,5)\}$.

If $f_i \subset t$ and $s$ is correctly generated, it's easy to see that these two multisets are equal. On the other hand, if these two multisets are equal, then we can categorize $(s_i, s_{i+1})$ into two multisets:

1. $\{(s_i, s_{i+1})\}$ where $s_i = s_{i+1}$
2. $\{(s_i, s_{i+1})\}$ where $s_i \ne s_{i+1}$

Since $t_i \ne t_{i+1}, \forall i \in [n]$, we must have the first multiset equals to ${(f_i, f_i)}$ and the second one equals to $\{(t_i, t_{i+1})\}$. Then it's easy to prove that we must have $\forall i \in [n], \exists j \in [n+1], f_i = t_j$, and therefore $s$ is the sorted array of $f+t$ based on the order of $t$ (we left the proof as exercise).

Equivalently, the prover can prove the equality of these two multisets with random $\beta \in \mathbb{F}$ provided by the verifier:

If two multisets A and B are equal, then applying the same random linear combination function $h(x, y) = x + \beta y$ (where $\beta$ is a randomly selected field element) to each of their elements should result in two new multisets A' and B' that are also equal (except with very small probability, according to the Schwartz-Zippel lemma).

Applying $h$ to each tuple in set 1:
For $(f_i, f_i)$, $h(f_i, f_i) = f_i + \beta f_i = (1 + \beta)f_i$
For $(t_i, t_{i+1})$, $h(t_i, t_{i+1}) = t_i + \beta t_{i+1}$
Transformed set 1': $\{(1 + \beta)f_i\} + \{t_i + \beta t_{i+1}\}$

Applying $h$ to each tuple $(s_i, s_{i+1})$ in set 2:
$h(s_i, s_{i+1}) = s_i + \beta s_{i+1}$
Transformed set 2': $\{s_i + \beta s_{i+1}\}$

- $\{(1+\beta) f_i\} + \{t_i + \beta t_{i+1}\}$
- $\{s_i + \beta s_{i+1}\}$

Note that the purpose here is to address how to transform the comparison of tuples $(x, y)$ (i.e., checking if multiset $\{(f_i, f_i)\} + \{(t_i, t_{i+1})\}$ equals $\{(s_i, s_{i+1})\}$) into a form that's easier to process with polynomials.

With another random $\gamma' \in \mathbb{F}$ from the verifier, the prover can prove the multiset equality by proving:

- $\prod_{i=1}^{n} ((1+\beta) f_i + \gamma') \prod_{i=1}^n (t_i + \beta t_{i+1} + \gamma') = \prod_{i=1}^{2n} (s_i + \beta s_{i+1} + \gamma')$

In Plookup paper, they use $\gamma' = (1+\beta) \gamma$, so the proof becomes:

- $(1+\beta)^n \prod_{i=1}^{n} (f_i + \gamma) \prod_{i=1}^n (t_i + \beta t_{i+1} + (1+\beta) \gamma) = \prod_{i=1}^{2n} (s_i + \beta s_{i+1} + (1+\beta) \gamma)$

Let $h_1$ be the first $n+1$ elements of $s$, and $h_2$ be the last $n+1$ elements. Here we must have $h_{1_{n+1}} = h_{2_1}$ since $|s| = 2n+1$. The $R.H.S$ of the above equation can be revised to

- $\prod_{i=1}^{n} (h_{1_i} + \beta h_{1_{i+1}} + (1+\beta) \gamma) (h_{2_i} + \beta h_{2_{i+1}} + (1+\beta) \gamma)$

Vector $h1$: Take the first $n+1$ elements of $s$, i.e., $h1 = (s_1, s_2, ..., s_{n+1})$.
Vector $h2$: Take the last $n+1$ elements of $s$, i.e., $h2 = (s_{n+1}, s_{n+2}, ..., s_{2n+1})$.

Here we split it into two halves, which will be explained later.

## Turn into Polynomial proof

To prove the grand product, Plookup uses the techniques similar to Plonk. Let $a_i = (1+\beta) (f_i + \gamma) (t_i + \beta t_{i+1} + (1+\beta) \gamma)$, $b_i = (h_{1_i} + \beta h_{1_{i+1}} + (1+\beta) \gamma) (h_{2_i} + \beta h_{2_{i+1}} + (1+\beta) \gamma)$, and we want to prove that $\prod_{i=1}^n a_i = \prod_{i=1}^n b_i$. This is just shortening the expressions.

Let $Z_1 = 1, Z_{i+1} = (a_i/b_i) Z_i$, the prover wants prove that $Z_{n+1} = Z_1 = 1$, and $\{Z_i\}$ is properly generated. Also, the prover needs to prove that $h_{1_{n+1}} = h_{2_1}$.
This holds because:

$a1 * a2 * ... * an$ (numerator)
$b1 * b2 * ... * bn$ (denominator)

The division should equal 1, so $Z1 = 1$ and $Z$ is a cumulative product process.

To prove that $Z_{i+1} = (a_i/b_i) Z_i$, we can prove that $Z_i a_i - Z_{i+1} b_i = 0, \forall i \in [n]$. In the Polynomial manner, it is to show that

$(x-g^{n+1})(Z(x) (1+\beta) (f(x) + \gamma) (t(x) + \beta t(g \cdot x) + (1+\beta) \gamma) - \\ Z(g \cdot x) (h_1(x) + \beta h_1(g \cdot x) + (1+\beta) \gamma) (h_2(x) + \beta h_2(g \cdot x) + (1+\beta) \gamma)) = 0$

This is a bit complex, let's discuss it in three parts:

Part one:
$Z(x) (1+\beta) (f(x) + \gamma) (t(x) + \beta t(g \cdot x) + (1+\beta) \gamma)$

This corresponds to the numerator part, where all $n+1$ parts are expressed using $g*x$.
It can be simplified as $Z_i * a_i$.

Part two:
$Z(g \cdot x) (h_1(x) + \beta h_1(g \cdot x) + (1+\beta) \gamma) (h_2(x) + \beta h_2(g \cdot x) + (1+\beta) \gamma)$

This corresponds to the denominator part.
It can be simplified as $Z_{i+1} * b_i$.

After simplification, we get:
$(x-g^{n+1}) * ((Z_i * a_i) - (Z_{i+1} * b_i)) = 0$
This differs from $Z_{i+1} = (a_i/b_i) Z_i$ only by the front factor.

Before discussing the third part, let's talk about the core constraint in the first two parts:

Range of the recursive relationship: This core constraint mainly describes the transition process of $Z$ on points in domain $H$ from $g^1$ to $g^n$:
When $x = g^1$, it constrains the value of $Z(g^2)$ relative to $Z(g^1)$.
When $x = g^2$, it constrains the value of $Z(g^3)$ relative to $Z(g^2)$.
...
When $x = g^n$, it constrains the value of $Z(g^{n+1})$ relative to $Z(g^n)$.

The beginning and end need to be constrained by other constraints.

Where $g$ is the root of unity of order $n+1$. With $L_i$ be the $i^{th}$ Lagrange polynomial over $\{g^i\}_{i=1}^{n+1}$, the other proofs can be done as follows:
These boundary conditions need to be proven:
- to show $Z_1 = 1$, prove $L_1(x)(Z(x)-1) = 0$ (this is the starting point)
- to show $Z_{n+1} = 1$, prove $L_{n+1}(x)(Z(x)-1) = 0$ (this is the endpoint)
- to show $h_{1_{n+1}} = h_{2_1}$, prove $L_{n+1}(x)(h_1(x) - h_2(gx)) = 0$

If we try to apply the core constraint at $x = g^{n+1}$, it would constrain the value of $Z(g^{n+2}) = Z(g^1)$ relative to $Z(g^{n+1})$.
However, the values of $Z(g^1)$ and $Z(g^{n+1})$ are already independently determined by the boundary conditions (both should be 1).
Therefore, enforcing the core constraint at point $x = g^{n+1}$ is unnecessary, and may even conflict with the boundary conditions (if the prover cheats, $Z(g^{n+1})$ might not equal 1, but the core constraint might still happen to hold).

Now let's look at the third part:
$(x-g^{n+1})$
The function of $(x - g^{n+1})$:
When $x$ is any point in $H$ except $g^{n+1}$ (i.e., $g^1, ..., g^n$), the factor $(x - g^{n+1})$ is non-zero. For the entire expression to equal zero, the core constraint itself must equal zero. This successfully enforces the recursive relationship at the $n$ points from $g^1$ to $g^n$.
When $x = g^{n+1}$, the factor $(x - g^{n+1})$ equals zero. Therefore, the entire expression $0 \cdot (\text{core constraint})$ necessarily equals zero, regardless of the value of the core constraint at point $x = g^{n+1}$.
Effect: This factor acts like a "switch" that ensures the core constraint must hold at the points that need to be checked ($g^1$ to $g^n$), while automatically satisfying the condition at the point that doesn't need to be checked ($g^{n+1}$), thereby precisely limiting the checking range to the $n$ points required by the protocol.

Now we describe the whole Plookup protocol (w/ ideal party $I$, paper section 3.1)

1. Prover sends $f, h_1, h_2$ to $I$.
2. Verifier chooses random $\beta, \gamma$ and sends to prover.
3. Prover computes $Z = \{\prod_{j=1}^i a_i / \prod_{j=1}^i b_i\}_{i \le n+1}$. Specifically, $Z_1 = Z_{n+1} = 1$. Prover sends $Z$ to $I$.
4. Verifier ask $I$ to check the following equations hold for all $x \in H$:
    1. $L_1(x)(Z(x)-1) = 0$
    2. $(x-g^{n+1}) (Z(x) a(x) - Z(g \cdot x) b(x)) = 0$, where $a(x) = (1+\beta) (f(x) + \gamma) (t(x) + \beta t(g \cdot x) + (1+\beta) \gamma)$, $b(x) = (h_1(x) + \beta h_1(g \cdot x) + (1+\beta) \gamma) (h_2(x) + \beta h_2(g \cdot x) + (1+\beta) \gamma)$
    3. $L_{n+1}(x) (h_1(x)-h_2(g \cdot x)) = 0$
    4. $Z_{n+1} = 1$ ⇒ $L_{n+1}(Z(x)-1) = 0$

## Replace ideal party with polynomial commitment

The original Plookup paper only provides the protocol with ideal party $I$. Our implementation, which based on Kevaundray's work, uses the technique similar to Plonk (or Plonkup) that makes use of KZG commitment to provide the zero-knowledge proof for polynomials.

Instead of sending polynomials to $I$, the prover commit $f, h_1, h_2, Z$ and a "quotient poly" $q$. The prover uses $q$ to prove that above a~d are satisfied. We want to check the polynomial on every points in $\{g^i\}_{i=1}^{n+1}$, so the vanish polynomial $v(x) = (x-g)(x-g^2)\cdots(x-g^{n+1}) = (x^{n+1}-1)$. The KZG commitment of $q$ is constructed as follows:

- to prove that $P_a(x) = L_1(x)(Z(x)-1) = 0$, commit $P_a(x)/v(x)$
- to prove that $P_b(x) = 0$, commit $P_b(x)/v(x)$
- to prove that $P_c(x) = L_{n+1}(x) (h_1(x)-h_2(g \cdot x)) = 0$, commit $P_c(x)/v(x)$
- to prove that $P_d(x) = L_{n+1}(x)(Z(x)-1) = 0$, commit $P_d(x)/v(x)$
- instead of committing all 4 polynomials, we have $q(x) = (P_a(x) + \delta P_b(x) + \delta^2 P_c(x) + \delta^3 P_d(x)) / v(x)$ for random $\delta$ and commit $q$ only.

With the commitments, the verifier can get $q(\zeta)$ for some $\zeta$. Then it wants to verify if the value is correct. To do so, the prover need to provide $f(\zeta), h_1(\zeta), h_2(\zeta), z(\zeta), h_1(g \cdot \zeta), h_2(g \cdot \zeta), z(g \cdot \zeta)$, and prove that the values are correct.

- For example, to prove knowledge of $f(\zeta)$, the prover commits $\frac{f(x)-f(\zeta)}{x-\zeta}$.
- To prove many polynomials at once, the prover computes
    1. $agg_1(x) = f(x) + \epsilon h_1(x) + \epsilon^2 h_2(x) + \epsilon^3 z(x) + \epsilon^4 q(x)$
    2. $agg_2(x) = h_1(g \cdot x) + \epsilon h_2(g \cdot x) + \epsilon^2 z(g \cdot x)$
    
    for random $\epsilon$ and prove knowledge on these two polynomials, i.e., commit $\frac{agg_1(x)-agg_1(\zeta)}{x-\zeta}$, $\frac{agg_2(x)-agg_2(\zeta)}{x-\zeta}$.
    

The verification process is as follows:

- First, the verifier computes $q(\zeta)$ with the help of the evaluations ($f(\zeta), \ldots, z(g \cdot \zeta)$).
- Next, the verifier verify the commitments of $agg_1, agg_2$
    - To verify the commitment of $agg_1$ (denote as $comm(agg_1)$, which is $\frac{agg_1(\tau) - agg_1(\zeta)}{\tau - \zeta}$ for some unknown crs $\tau$), the verifier verify the pairing $e(agg_1(\tau) - agg_1(\zeta), 1) = e(comm(agg_1), \tau - \zeta)$
    - To verify the commitment of $agg_2$ (denote as $comm(agg_2)$, which is $\frac{agg_2(\tau) - agg_2(g \cdot \zeta)}{\tau - g \cdot \zeta}$ for some unknown crs $\tau$), the verifier verify the pairing $e(agg_2(\tau) - agg_2(g \cdot \zeta), 1) = e(comm(agg_2), \tau - g \cdot \zeta)$
- The verifier accepts the proof if and only if both pairing equations hold.

## Implementation

Here we present some worth-mentioned implementation details.

### sorted\_by\_table

As mentioned above, we need to combine witness $f$ and public table $t$, and sorted by the order $t$. A simple way would be sorting both $t$ and $f + t$, which is what Plonkup does. However, we implement it in a more flexible way that allows the public table to be unsorted.

```python
def sorted_by_table(self, witness: list[int], table: list[int]):
    data = table + witness
    index = {}
    for i, t in enumerate(table):
        index[t] = i
    for w in witness:
        assert(w in index)
    return sorted(data, key=lambda x: index[x])
```

### Generate polynomials

To generate a polynomial from the values evaluated on the roots of unity, we follow Plonkathon's implementation (see `common_util/poly.py`), and some adjustment needs to be performed accordingly. 

The first is that we want to generate the polynomial of $f$ from the array with length $n$. However, the generator $g$ is of order $n+1$, so we need to pad $f$ to length $n+1$ and make it a polynomial. If we append a random number to $f$, then the polynomial would likely to have degree $n$, not $n-1$ as required in Plookup paper. However, we think that the degree problem does not affect the security of the protocol, so we simply append the last element of $f$ and make it a polynomial of degree $n$.

```python
def round_1(self, witness: list[Scalar]) -> Message1:
    ...
    self.f = list(map(Scalar, witness))
    self.f.append(self.f[-1])
    self.f_poly = Polynomial(self.f, Basis.LAGRANGE)
    ...
```

Second, the list of roots of unity (denote as $H$) is $[g, \ldots, g^{n+1}=1]$ in Plookup paper but $[1, \ldots, g^n]$  in Plonkathon's implementation. So we need to be careful about the Lagrange polynomials $L_1, L_{n+1}$ and equation b. In particular, we have equation b be $(x-g^n)(\ldots)$ instead of $(x-g^{n+1})(\ldots)$.

```python
def get_poly_b(self) -> Polynomial:
    front = Polynomial([-self.H[self.n], Scalar(1)], Basis.MONOMIAL)
    lhs = front * ...
    rhs = front * ...
```

Lastly, the polynomial multiplication in Plonkathon's implementation is a little tricky. In short, sometimes we need to use `ifft()` to get correct multiplication result.

## Reference

1. Plookup paper: [https://eprint.iacr.org/2020/315.pdf](https://eprint.iacr.org/2020/315.pdf)
2. Plookup implementation with KZG commitment in Rust: [https://github.com/kevaundray/plookup](https://github.com/kevaundray/plookup)
3. Plonk and Plookup introduction (CN): [https://github.com/sec-bit/learning-zkp/blob/develop/plonk-intro-cn/7-plonk-lookup.md](https://github.com/sec-bit/learning-zkp/blob/develop/plonk-intro-cn/7-plonk-lookup.md)
4. KZG commitment: [https://www.iacr.org/archive/asiacrypt2010/6477178/6477178.pdf](https://www.iacr.org/archive/asiacrypt2010/6477178/6477178.pdf)
5. Plonkup: [https://eprint.iacr.org/2022/086.pdf](https://eprint.iacr.org/2022/086.pdf)