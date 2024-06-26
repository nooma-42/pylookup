# Logup+ (Logup GKR)

This article assumes you understand sumcheck protocol and gkr

## Table & Notation

n = #row
M = #col

xi ∈ H_n
witness column: w1(X), ...W_M(X), in below example, we have w1 and w2

    w1(X)   w2(X)  
x1  1       2       
x2  2       1
x3  3       4 
x4  1       2

    t(X)    m(X)
x1  1       3
x2  2       3
x3  3       1
x4  4       1

## What we want to prove

We can use logarithmic derivative to represent the equality by summing over M columns and n rows. This corresponds to equation 2 in the paper.
1/X-1 + 1/X-2 + 1/X-2 + 1/X-1 + 1/X-3 + 1/X-4 + 1/X-1 + 1/X-2 = 3/X-1 + 3/X-2 + 1/X-3 + 1/X-4

we can reduce the form to a sumcheck with α given by verifier. We sum over following terms and check if it's equal to 0. (equation 3 in the paper)
X1: (2/α-1 - (1/α-1 + 1/α-2))
X2: (2/α-2 - (1/α-2 + 1/α-1))
X3: (1/α-3 - (1/α-3 + 1/α-4))
X4: (1/α-4)


## How do we represent this with the term that GKR can prove

We prove nominator and denominator separately. p is nominator and q is denominator

Before we go into the detail, You must know the L_k(Y, X). This is lagrange basis as introduced at the beginning of the paper. Simply imagine it like lagrange basis that you're familiar with, but this is rather in multilinear polynomial. The input is like 111111 1010111. If your input is same as the given point like input is 11111 and given interpolate at 11111. L_k(Y, X) returns 1 otherwise 0. Some other papers define it as eq. For example, Proof Arguments and Zero Knowledge.

Since GKR goes from top to bottom, there's X variable taking the random point and Y variable looping through the rows. The length of X and Y is n. As the layer goes down, the length of X increases and the length of Y decreases.

Following section 4. we have 2^k columns of length 2^n, then we have the equations as below.

p(X, Y) = L_k(Y, 1) * m(X) - ∑ L_k(Y, y) * 1
q(X, Y) = L_k(Y, 1) * (a - t(X)) - ∑ L_k(Y, y) (a - w(X))

for example, p(00, 0) and p(00, 1) are
p(00, 0) = L_k(0, 1) * m(X) - ∑ L_k(0, y) * 1 = 2
p(00, 1) = L_k(1, 1) * m(X) - ∑ L_k(1, y) * 1 = m(00) = 3

The summation p should be zero, but the q might not.

In fact we can concat X and Y to get Z and look at them as p(Z), for example, p(000, 1) is same as p(0001). We can further think of Z as X. These are just different name of variable. Therefore, we can apply gkr mentioned in section 3.2 with concated X
p_k(x) = ∑ (y∈H_k) L_k(Y, y) (p_k+1(y, +1) * q_k+1(y, -1) + p_k+1(y, -1) * q_k+1(y, +1))
q_k(x) = ∑ (y∈H_k) L_k(Y, y) (q_k+1(y, -1) * q_k+1(y, +1))

How to think of L_k()? this is the lagrange basis, but we don't really need to calculate it. We just need to have a function mapping the input to the output like below:
```python
def test2_w2(X: list[Scalar]) -> Scalar:
    result = {tuple([zero, zero]): Scalar(2), # This represent L(Y, 00) * 2
            tuple([zero, one]): Scalar(1), # This represent L(Y, 01) * 1 
            tuple([one, zero]): Scalar(4),
            tuple([one, one]): Scalar(2)}.get(tuple(X))
    if result is None:
        raise ValueError("Invalid input")
    else:
        return result
```

## What does this "fractional" GKR prove?

The equation stands for the addition of 2 fractional terms like below

p_k+1(y, -1)    p_k+1(y, +1)    (p_k+1(y, +1) * q_k+1(y, -1) + p_k+1(y, -1) * q_k+1(y, +1))
------------ + -------------- = -----------------------------------------------------------
q_k+1(y, -1)    q_k+1(y, +1)                    (q_k+1(y, -1) * q_k+1(y, +1))

Each layer prove the summation of fraction is correctly made at layer below.

At the top layer k = 0, we directly have the value, let's say
p0  = 0
q0  = 4800

And this fraction should be the summation of the fraction below
p0 / q0  = ∑(y∈H_n) p(y) / ∑(y∈H_n) q(y) 
the variable term disappear due to this is the first layer below
p0 = p1(+1) * q1(-1) - p1(-1) * q(+1)
q0 = q1(+1) * q1(-1)

Next layer 1, we have
p1(X) = ∑(y∈H_1) L_1(X, y) * (p2(y, +1) * q2(y, -1) - p2(y, -1) * q2(y, +1))
q1(X) = ∑(y∈H_1) L_1(X, y) * (q2(y, +1) * q2(y, -1))

