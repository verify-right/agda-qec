# Binary matrices and CSS codes

## Binary dot products

Work over the field $\mathbb{F}_2$. Addition is XOR and
multiplication is AND.

For two binary vectors

$$
a=(1,1,0),\qquad b=(1,1,1)
$$

their dot product is

$$
a\cdot b=1+1+0=0.
$$

The dot product counts the parity of the intersection
of their supports.

In Agda, a binary vector is represented by `Fin n → Bool`.
The theorem `dot-add` proves that the dot product
distributes over vector addition.

## Parity checks and syndromes

A parity-check matrix $H$ describes a binary linear code:

$$
C=\ker H=\{c: Hc=0\}.
$$

Suppose a codeword $c$ is corrupted by an error $e$.
The received word is $r=c+e$.

Its [syndrome](https://en.wikipedia.org/wiki/Decoding_methods#Syndrome_decoding)
is

$$
Hr=H(c+e)=Hc+He=He.
$$

The syndrome depends on the error, not on the original
codeword. This is what `syndrome-coset` proves.

## From classical checks to Pauli operators

The single-qubit Pauli operators satisfy

$$
X|v\rangle=|v+1\rangle,\qquad
Z|v\rangle=(-1)^v|v\rangle.
$$

Consequently,

$$
XZ=-ZX.
$$

For several qubits, binary vectors $x$ and $z$ describe
where X and Z operators act.

Two Pauli representatives $(x,z)$ and $(x',z')$
acquire the following relative sign when exchanged:

$$
(-1)^{z\cdot x'+z'\cdot x}.
$$

The exponent is their
[binary symplectic product](https://en.wikipedia.org/wiki/Symplectic_vector_space).

The Agda theorem `swap-sign` proves this identity
for every signed computational basis label.

For a pure X operator and a pure Z operator, the
symplectic product reduces to an ordinary binary dot product.
An even overlap means the operators commute.

## CSS codes

A [CSS code](https://en.wikipedia.org/wiki/CSS_code)
uses two binary parity-check matrices, $H_X$ and $H_Z$.

Their stabilizer generators must commute. By the preceding
calculation, this requires

$$
H_XH_Z^T=0.
$$

For example, take

$$
H_X=\begin{pmatrix}1&1&0\end{pmatrix},
\qquad
H_Z=\begin{pmatrix}1&1&1\end{pmatrix}.
$$

The two rows overlap at two positions, so their dot product
is zero. The X and Z checks commute.

This is the condition used by `css-sign`.

## A chain complex

Consider the sequence

$$
\mathbb{F}_2^{m_Z}
\xrightarrow{H_Z^T}
\mathbb{F}_2^n
\xrightarrow{H_X}
\mathbb{F}_2^{m_X}.
$$

The first map forms a combination of Z-stabilizer generators.
The second computes its X syndrome.

Since $H_XH_Z^T=0$, the composition is zero:

$$
\operatorname{im}H_Z^T\subseteq\ker H_X.
$$

This is the defining property of a
[chain complex](https://en.wikipedia.org/wiki/Chain_complex):
every boundary is a cycle.

The Agda theorems `boundary-cycle` and `cycle-rows`
prove both directions of the equivalence between the
chain condition and row orthogonality.

A cycle need not be a boundary. The quotient

$$
\ker H_X/\operatorname{im}H_Z^T
$$

describes Z-type logical operators modulo stabilizers.

This distinction is essential when defining quantum code
distance: a zero-syndrome error may act nontrivially on
encoded information.

The quotient gives the mathematical motivation for later
developments; it is not constructed in these two modules.

## Agda sources

- [Binary matrix operations](../src/Coding/Binary.agda).
- [Pauli commutation](../src/Coding/Symplectic.agda).
- [Finite sums](../src/Algebra/FiniteSums.agda).