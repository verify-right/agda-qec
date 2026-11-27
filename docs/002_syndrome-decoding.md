# Syndrome decoding and Hamming codes

## Locating an error

Let $H$ be a binary parity-check matrix and $c$ a
codeword satisfying $Hc=0$.

Write $e_j$ for the vector containing a one at coordinate
$j$ and zeros elsewhere.

If bit $j$ is flipped, the received word is

$$
r=c+e_j.
$$

By linearity,

$$
Hr=H(c+e_j)=He_j.
$$

Multiplication by $e_j$ selects column $j$ of $H$.
The syndrome therefore identifies the erroneous coordinate,
provided the columns are distinct.

Adding $e_j$ again recovers the original word:

$$
r+e_j=c+e_j+e_j=c.
$$

This is the argument behind `flip-syndrome` and `one-error`.

## The seven-bit Hamming code

The [Hamming code](https://en.wikipedia.org/wiki/Hamming(7,4))
uses the parity-check matrix

$$
H=
\begin{pmatrix}
1&0&1&0&1&0&1\\
0&1&1&0&0&1&1\\
0&0&0&1&1&1&1
\end{pmatrix}.
$$

Its columns are the binary representations of the integers
1 through 7, with the least significant bit first.

Suppose the sixth bit is flipped. The syndrome is

$$
s=\begin{pmatrix}0\\1\\1\end{pmatrix}.
$$

Reading this as a binary number gives

$$
0+2+4=6.
$$

The decoder flips the sixth bit again.

Agda uses zero-based indices, so the corresponding
coordinate has index 5.

## Why two conditions?

Distinct columns ensure that two different single-bit
errors cannot produce the same syndrome.

Nonzero columns ensure that a single-bit error cannot
produce the same syndrome as an uncorrupted codeword.

The generic decoder proves these properties separately.
The Hamming instance satisfies both.

## Constructive search

The decoder uses `any?` and `all?` from Agda stdlib
to search the columns of the matrix.

Its result has type

```agda
Dec (Σ (Fin n) (λ j → Column j ≐ s))
```

A successful search returns both the coordinate and a
proof that its column equals the syndrome.

An unsuccessful search returns a proof that no such
coordinate exists.

The correctness proof excludes this second case whenever
the received word differs from a codeword in exactly one
coordinate.

The same search function works for any binary matrix.
Only its correctness guarantees require assumptions
about the columns.

## Connection to quantum error correction

CSS codes also use binary parity-check matrices to
compute syndromes.

However, quantum errors need only be corrected modulo
stabilizers. Different errors can have the same syndrome
and still be equivalent on encoded information.

The classical decoder developed here does not yet
formalize that equivalence.

## Agda sources
- [Generic decoder](../src/Coding/Decoder.agda).
- [Hamming code](../src/Coding/Hamming.agda).