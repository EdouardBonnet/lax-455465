This submission concerns the deterministic algorithms behind the
multicommodity flow–cut theorems of Leighton and Rao. The general statement
allows rational product demands, zero-weight transit vertices, and directed
or undirected capacities. One deterministic algorithm runs in time polynomial
in the binary encoding size of the rational input and returns a positive-demand
cut and an exact rational concurrent flow satisfying
$\operatorname{ratio}(S)\le C\log_2(p)f$, where $p$ is the number of
positive-weight vertices. Directed, undirected, and uniform variants are
corollaries of this common guarantee.

The submission also includes the deterministic uniform short-path flow
construction of Theorem 18, with its simultaneous flow-value and path-length
guarantees. Algorithms use the exact LP solver of
[lax-109476](https://laxarchive.org/lax-109476/), the registered word RAM of
[lax-808846](https://laxarchive.org/lax-808846/) and the polynomial-time
predicate of [lax-759944](https://laxarchive.org/lax-759944/), measured in
binary rational input size and requiring exact encoded outputs.
