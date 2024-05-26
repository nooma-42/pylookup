# Logup+ (Logup GKR)

## Table & Notation

n = #row
M = #col

xi ∈ H_n
witness column: w1(X), ...W_M(X)

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

we can reduce the form to a sumcheck with α given by verifier. We sum over following terms and check if it's equal to 0. (equation 3)
X1 (2/α-1 - (1/α-1 + 1/α-2)) 
X2 (2/α-2 - (1/α-2 + 1/α-1))
X3 (1/α-3 - (1/α-3 + 1/α-4))
X4 (1/α-4)


## How do we represent this with the term that GKR can prove

We prove nominator and denominator separately. p is nominator and q is denominator

Before we go into the detail, You must know the L_k(Y, X). This is lagrange basis as introduced at the begining of the paper. Simply imagine it like lagrange basis that you're familiar with, but this is rather in multilinear polynomial. The input is like 111111 1010111. If your input is same as the given point like input is 11111 and given interpolate at 11111. L_k(Y, X) returns 1 otherwise 0. Some other papers define it as eq. For example, Proof Arguments and Zero Knowledge.

Since GKR goes from top to bottom, there's X variable taking the random point and Y variable looping through the rows. The length of X and Y is n. As the layer goes down, the length of X increases and the length of Y decreases.

Following section 4. we have 2^k columns of length 2^n, then we have the equations as below.

p(X, Y) = L_k(Y, 1) * m(X) - ∑ L_k(Y, y) * 1
q(X, Y) = L_k(Y, 1) * (a - t(X)) - ∑ L_k(Y, y) (a - w(X))

At the top layer k = 0, we have original equation
p0  = ∑(x∈H_0, y∈H_0) (L0(Y, 1) m(x) - ∑ L0(X, x) 1)
    lagrange basis is 1 in this case, 
    TODO doesn't seems to work for base case?

    prover has to calculate this function and add to proof. 
    There's also a relationship between this layer and the next layer. We're going to use this relationship for the next layer.
    concat xy and get z
    = ∑(z ∈H_0) L0(Z, z) * (p1(+1) * q1(-1) - p1(-1) * q1(+1)) 
    = p1(+1) * q1(-1) - p1(-1) * q1(+1)
    which expects to be 0
    =0

q0  = ∑(x∈H_0, y∈H_0) (L0(Y, 1)(a - t(y)) - ∑(y∈H_0\{1}) L0(Y, 1)(a - w(y)))
    = ∑(x∈H_0) L0(X, x) * (q1(+1) * q1(-1)) = q1(+1) * q1(-1)

p0 / q0  = ∑(y∈H_n) p(y) / ∑(y∈H_n) q(y) 

Next layer 1, we have
p1(X)   = ∑(x∈H_1, y∈H_0) (L_1(Y, 1) * m(X) - ∑ L_1(Y, y) * 1)
        Here L_1(Y, 1) and L_1(Y, y) are 1
        = ∑(x∈H_1) (m(X) - ∑ 1)

        = ∑(y∈H_1) L_1(X, 1) * p2(x, +1) * q2(x, -1) - p2(-1) * q2(+1)

q1(x)   = ∑(y∈H_n) L_k(Y, 1) * (a - t(X)) - ∑ L_k(Y, y) (a - w(X))
        = q2(x, +1) * q2(x, -1)

p1(x) / q1(x) = ∑(y∈H_n-1) (p1(X, y) /  q1(X, y))

...

At layer n, we have

p1(X)   = ∑(y∈H_n-1) L_1(Y, 1) * m(X) - ∑ L_1(Y, y) * 1
        = ∑(y∈H_1) p2(x, +1) * q2(x, -1) - p2(-1) * q2(+1)

q1(x)   = ∑(y∈H_n) L_k(Y, 1) * (a - t(X)) - ∑ L_k(Y, y) (a - w(X))
        = q2(x, +1) * q2(x, -1)


...

At layer n + 1, we have

...

At layer n + k, we have