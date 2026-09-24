# Corollary 24 and Theorem 4: common woven proof

**Status (24 September 2026).** This is a self-contained mathematical
proof manuscript for both endpoints. Sections 1–6 give the shared
induction and endpoint deductions; Sections 7–8 prove the auxiliary
chain; Appendices A–F prove every non-elementary input used there.
The external papers are cited for provenance and comparison, not as
unproved proof leaves. The argument has undergone separate adversarial
audits of its main auxiliary proofs. Nothing here is claimed to be a
Lean-checked proof.

The mathematical sources are the [main paper](../paper/main.tex), especially
Lemma 23 and Corollary 24, and [Delcourt–Postle, arXiv:2108.01633v5](https://arxiv.org/pdf/2108.01633v5),
especially Theorems 1.6 and 7.1. The latter paper's printed proof needs several
repairs before it can serve as a complete proof; these are recorded below.

## 1. Conventions and target statements

All graphs are finite and simple. An $r$-connected graph has more than $r$
vertices and remains connected after deletion of fewer than $r$ vertices.
Thus $\kappa(X-U)\ge\kappa(X)-|U|$ whenever the right side is positive.
Write $\chi(X[U])$ for the chromatic number induced on $U$. We use

$$\chi(X-U)\ge\chi(X)-\chi(X[U]),\qquad
  \chi(X-U)\ge\chi(X)-|U|.$$

A $K_a$ model has $a$ disjoint connected branch sets, with an edge between
every two. It is rooted at $r_1,\ldots,r_a$ if branch $i$ contains $r_i$
and no other root. A linkage for indexed pairs $(s_j,t_j)$ consists of
disjoint paths joining those pairs. An $A$–$B$ path is
trimmed to meet $A\cup B$ only at its designated ends. Different pairs have disjoint terminal
sets, but $s_j=t_j$ is permitted and is represented by a one-vertex path.
Roots may be terminals.

For $a\ge1$ and $b\ge0$, write $W(a,b;X)$ if, for every choice of $a$
distinct roots and **at most** $b$ indexed terminal pairs in $X$, there are
a rooted $K_a$ model $\mathcal M$ and a linkage $\mathcal P$ with

$$V(\mathcal M)\cap V(\mathcal P)
  =\{\hbox{roots that are terminals of the linkage}\}.$$

The “at most” convention is important. Delcourt–Postle Definition 5.12
quantifies over exactly $b$ pairs. Its property implies $W(a,b;X)$ whenever
$|X|\ge a+2b$: for $j<b$ pairs, pad with $b-j$ disjoint pairs of fresh
vertices outside the original roots and terminals, apply the exactly-$b$
property, and discard the dummy paths. Every graph to which we apply this
conversion has the required order. Without it, their Lemma 5.15 is false by
vacuity for small $X$.

For a graph $Y$ and $s\ge0$, say that $Y$ is $s$-*chromatic-separable* if
there are two vertex-disjoint induced subgraphs of $Y$, both with chromatic
number at least $\chi(Y)-s$. Induced closures may be taken after finding
arbitrary subgraphs.

**Corollary 24 (main paper).** Let $t\ge100$, let $T$ be the least power of
three at least $t$, and let $d\ge1$ be an integer. Suppose that for every
integer scale $a=(2/3)^iT>T/\sqrt{\log T}$ with $i\ge0$, each induced
$K_{14a}$-minor-free subgraph $Y$ of $G$ with $\chi(Y)>28da$ is
$14da$-chromatic-separable. If $G$ has no $K_t$ minor, then

$$\chi(G)<3\bigl(10^6(d+1)+62000\bigr)t.$$

**Theorem 4 (main paper; Delcourt–Postle Theorem 1.6).** There is an
absolute integer $C\ge1$ such that, for every $t\ge3$ and every
$K_t$-minor-free $G$,

$$\chi(G)\le Ct\bigl(1+f_C(G,t)\bigr),$$

where, with the empty maximum interpreted as zero,

$$f_C(G,t)=\max\left(\{0\}\cup
 \left\{\frac{\chi(H)}{q}:\begin{array}{l}
 H\subseteq G,\quad H\text{ has no }K_q\text{ minor},\\
 q\in\mathbb Z,\quad t/\sqrt{\log t}\le q\le t,\\
 |H|\le Cq(\log q)^4
 \end{array}\right\}\right).$$

The same $C$ occurs in the chromatic bound and the order cutoff.

## 2. Shared input contracts

The common proof uses the following statements. They are isolated here so
their eventual standalone proofs can replace the contracts without changing
the outer induction.

* **(GN)** If $\chi(X)\ge7r$, an induced $r$-connected $X'\subseteq X$
  satisfies $\chi(X')\ge\chi(X)-6r$. The additive form is implicit in
  [Girão–Narayanan](https://arxiv.org/pdf/2004.00533); Appendix A below
  includes its proof.
* **(L)** Every $16\ell$-connected graph is $\ell$-linked. In fact $10\ell$
  connectivity suffices by
  [Thomas–Wollan](https://thomas.math.gatech.edu/PAP/klink.pdf). The weaker
  $L=16$ is sufficient for the exact constants of Corollary 24.
  Appendix D proves this weaker form with no external linkedness input.
* **(KR)** If $X$ is $r$-connected and has a $K_{2r}$ minor, then every
  set of $r$ distinct vertices roots a $K_r$ model in $X$.
  This is Kawarabayashi's rooted-minor lemma. Appendix B proves it
  from Menger via a separator dichotomy.
* **(KT)** Every nonempty $X$ with
  $|E(X)|/|X|\ge30r\sqrt{\log r}$, $r\ge2$, has a $K_r$ minor.
  Consequently every $K_r$-minor-free $X$ obeys
  $\chi(X)\le60r\sqrt{\log r}+1$: an $m$-chromatic graph has an
  $m$-critical subgraph of minimum degree at least $m-1$.
  Appendix E proves this quantitative density theorem.
* **(M)** The set form of Menger's theorem: the maximum number of
  disjoint $A$–$B$ paths equals the minimum size of an $A$–$B$
  vertex separator. We use the version permitting vertices of $A\cup B$
  in a separator. Appendix A gives a reduction to integral max flow.

Theorem 4 additionally needs the following Delcourt–Postle inputs, with
constants allowed to increase. Section 7 records their dependency chain.

* **(SC)** There is $C_s$ such that, if $q\ge3$ and $k\ge q$
  are integers,
  $X$ has no $K_q$ minor and density at least $C_s k$, then $X$
  contains a $k$-connected induced subgraph $H$ with
  $|H|\le C_s^2q(\log q)^3$ (DP Theorem 2.3).
* **(CI)** There is $C_i$ such that, with
  $$g_{C_i}(X,q)=\max\bigl(\{0\}\cup
  \{\chi(H)/q:H\subseteq X,\ |H|\le C_iq(\log q)^4,
  \ H\text{ has no }K_q\text{ minor}\}\bigr),$$
  if $X$ has no $K_q$ minor and $\chi(X)\ge
  2C_iq(1+g_{C_i}(X,q))$, then $X$ is
  $C_iq(1+g_{C_i}(X,q))$-chromatic-separable
  (the contrapositive of DP Lemma 2.5).

Sections 7–8 prove SC and CI using the density and rooted-minor
theorems proved in Appendices E–F. Section 9 records the full
dependency graph and repairs to the published deductions.

## 3. Elementary common lemmas

### 3.1 A rooted minor yields wovenness

For distinct roles, suppose $X$ is $n$-connected and contains a
$K_{2n}$ minor. By KR it has a $K_n$ model rooted at any $n$ prescribed
distinct vertices. Given $a$ roots and $b$ disjoint terminal pairs
with $n=a+2b$, assign one role to each branch. Retain the $a$ root
branches. For every terminal pair, join its two terminal branches
by a model edge and take the resulting path within these branches.
This gives a woven solution for distinct roles.

When roles coincide, the actual sufficient hypothesis is stronger:
let $U$ be the set of original occupied vertices, choose a distinct
neighbor proxy outside $U$ for every one of the $n$ occurrences, and
require the *normalized graph* $X-U$ to be $n$-connected with a
$K_{2n}$ minor. At each greedy choice at most $2n-1$ vertices are
forbidden, so minimum degree at least $2n$ in $X$ suffices for
choosing proxies. Apply KR to the normalized graph at the proxies.
Extend root branches and linkage ends back along their proxy edges.
For a singleton pair discard its proxy path and use the one-vertex
path. In the outer induction $n=7a$, and the minor test takes place
in this normalized graph, where connectivity remains at least $7a$.

### 3.2 Redundant Menger and the mixed fan

Let $A_1,A_2,B$ be disjoint nonempty sets. For each $i=1,2$, suppose
there are $2|A_i|$ paths from $A_i$ to $B$ in $X-A_{3-i}$, disjoint
outside $A_i$, exactly two starting at each vertex of $A_i$. Then there
are $|A_1|+|A_2|$ disjoint paths from $A_1\cup A_2$ to $B$.

Indeed, if not, M gives a separator $Q$ of size below
$|A_1|+|A_2|$. Put $A_i'=A_i-Q$ and $Q'=Q-(A_1\cup A_2)$, and relabel
so $|A_1'|\ge|A_2'|$. Then
$|Q'|<|A_1'|+|A_2'|\le2|A_1'|$. But the
$2|A_1'|$ paths starting in $A_1'$ avoid $A_2$ and are disjoint outside
$A_1$, so one avoids $Q'$, contradicting that $Q$ separates.

For the mixed fan used later, let $|Z|=7a$. Suppose there are two
paths from each $z\in Z$ to a hub $H$, disjoint outside $Z$ and avoiding
a residual vertex set $U$; and $2a$ disjoint $U$–$H$ paths avoiding
$Z$, trimmed to meet $U\cup V(H)$ only at their ends.
Pair the $2a$ starting vertices in $U$, add a new vertex for
each pair and join it to the pair's members. The redundant Menger
lemma applies to $Z$ and the $a$ new vertices. Delete those new
vertices afterward. In the graph consisting only of the supplied
paths and these new edges, each starting vertex in $U$ has degree
one after deletion, because the first fan avoided $U$; it cannot be
internal to a resulting path. We obtain $8a$ disjoint paths to $H$,
one from every $z\in Z$ and $a$ from distinct vertices of $U$, with
interiors outside $Z\cup U\cup V(H)$.

### 3.3 Rerouting a linkage through a woven child

Let $H\subseteq X$ satisfy $W(a,b;H)$, fix $a$ roots in $H$, and let
$\mathcal P$ be a linkage of at most $b$ pairs in $X$. For every path
that meets $H$, take its first and last vertices in $H$ from its
respective ends. These inner pairs are indexed and disjoint across
paths. Apply $W(a,b;H)$ to them, obtaining a rooted model and inner
linkage. Replace the segment of each original path between its first
and last hits by the corresponding inner path. The untouched outer
segments have no vertices in $H$, so the new paths remain disjoint.
The resulting linkage $\mathcal P'$ and model $\mathcal M$ obey

$$V(\mathcal P')\subseteq V(\mathcal P)\cup V(H),\qquad
V(\mathcal P')\cap V(\mathcal M)
 \subseteq R\cap V(\mathcal P).$$

If every root is an endpoint of an original path, the latter
intersection is exactly $R$. Apply this successively to three
disjoint children: later rerouting uses only the old linkage and
the current child, so it preserves the intersection with models
in earlier children.

### 3.4 Two paths from each proxy

Suppose $Z$ consists of $7a$ vertices in an $r$-connected graph $X$,
$H\subseteq X-Z$ has at least $14a$ vertices, and $r\ge21a$. Delete
$Z$ and replace each $z$ by two clones, each adjacent to its former
neighbors outside $Z$. There are $14a$ disjoint clone–$H$ paths.
For if a set of fewer than $14a$ vertices separates all clones from
$H$, some clone of some $z$ survives. Delete the separator's original
vertices and the other $7a-1$ members of $Z$ in $X$; fewer than
$21a$ vertices are removed. The surviving $z$ connects to an
undeleted vertex of $H$, producing a clone–$H$ path avoiding the
separator, contradiction. M now supplies the paths. Collapsing each
clone pair gives two paths per proxy, disjoint outside $Z$, with
distinct ends in $H$. Shorten each path to an induced path.
Give each of the $14a$ paths a private two-color palette.
At each shared proxy, use the palette of one incident path
and color the other path minus that proxy with its own palette.
Cross-path edges then join distinct palettes, so the induced
union costs at most $28a$ colors.

## 4. The shared outer induction

We now prove a parameterized recursion, in a form directly specialized
twice below. Fix a power of three $T\ge3$, a host graph $G$, an integer
$K\ge\max\{28,2L+1\}$ with $L=16$, a fixed nonnegative real $U$, a number
$B\ge0$, and nonnegative functions $h(a)$ and $\sigma(a)$ on the
integer scales $a=(2/3)^iT$ with $i\ge0$. Assume, at every nonbase scale
$a>T/\sqrt{\log T}$:

1. Every induced $K_{14a}$-minor-free $X\subseteq G$ with
   $\kappa(X)\ge(K-14)a$ and $\chi(X)\ge U+(B-14)a$
   contains an induced hub $H\subseteq X$ with
   $\kappa(H)\ge4La$ and $\chi(H)\le h(a)$.
2. Every induced $K_{14a}$-minor-free $Y\subseteq G$ occurring after
   deletion of the proposed inner roots and their neighbors, with
   $\chi(Y)>2\sigma(a)$, has two disjoint induced subgraphs of
   chromatic number at least $\chi(Y)-\sigma(a)$ each. The same
   assertion applies to the first selected subgraph, provided its
   chromatic number is greater than $2\sigma(a)$.
3. The numerical budget conditions listed just below hold.

The separation condition can equivalently be imposed on *all* eligible
induced $Y\subseteq G$; this stronger, simpler form is what both
specializations supply. The hub contract is likewise only used on the
normalized, proxy-deleted graph.

For clarity, here are sufficient numerical conditions, rather than a
claim that they are sharp. At a nonbase scale put

$$D_0(a)=(14+28)a+h(a),\qquad
  D_1(a)=D_0(a)+6Ka+3a.$$

Require the hub contract's hypotheses after at most $14a$ vertex
deletions; require

$$U+Ba-D_0(a)\ge7Ka,\qquad
  U+Ba-D_1(a)-2\sigma(a)\ge7Ka,$$

and require the first and second separation inputs to exceed
$2\sigma(a)$. Finally require

$$\boxed{\quad B a/3\ \ge (45+12K)a+h(a)+2\sigma(a).\quad} \tag{4.1}$$

For a base scale $a\le T/\sqrt{\log T}$ require
$U+(B-7)a>840a\sqrt{\log(14a)}+1$; KT then forces the
$K_{14a}$ minor in the normalized graph. The inequality is strict
because the KT coloring bound is non-strict.

**Claim.** Under these contracts, every induced $F\subseteq G$ with
$\kappa(F)\ge Ka$ and $\chi(F)\ge U+Ba$ satisfies $W(a,3a;F)$.

*Proof.* Induct downward through the integer scales. Fix arbitrary
roots and at most $3a$ terminal pairs. Pad to exactly $3a$ pairs
using distinct fresh vertices outside all original roles; this
is possible since $|F|>Ka\ge7a$. After constructing the
exactly-$3a$ solution, discard the dummy paths. Their ends
avoid the roots, so the required model–linkage intersection
is unchanged. We may thus work with three-$a$ pairs and
$7a$ indexed roles.
Let $Z_0$ be the set of vertices occupying roles. Greedily choose a
distinct adjacent proxy outside $Z_0$ for each role: at any stage
fewer than $14a$ vertices are forbidden and $\delta(F)\ge Ka$.
Set $F_0=F-Z_0$. It has connectivity at least $(K-7)a$ and
chromatic number at least $U+(B-7)a$. A woven solution for the
distinct proxies in $F_0$ lifts to the original roles using the
chosen edges; singleton pairs use their original vertex as their
path. No forbidden model–linkage intersection is introduced.

If $F_0$ contains a $K_{14a}$ minor, KR at order $7a$ and Section
3.1 finish. This case also holds at every base scale by KT and the
base inequality. Hence assume $a>T/\sqrt{\log T}$ and $F_0$ has
no $K_{14a}$ minor. Let $Z$ be the proxy set. Apply the hub contract
to $F_0-Z$, obtaining $H_0$ with connectivity at least $4La$ and
chromatic cost at most $h(a)$. Section 3.4 supplies a double fan
from $Z$ to $H_0$, since $\kappa(F_0)\ge(K-7)a\ge21a$.

Delete $Z$, $H_0$, and the fan. The residual induced graph has
chromatic number at least $U+Ba-D_0(a)$: the original role deletion
cost at most $7a$, proxy deletion another $7a$, the hub costs
$h(a)$, and the fan costs $28a$. By the first numerical condition,
GN produces an induced $Ka$-connected graph $F_3$, disjoint from
the hub and fan, with

$$\chi(F_3)\ge U+Ba-D_0(a)-6Ka. \tag{4.2}$$

It is enough to show that $F_3$ has a rooted $K_a$ model for every
choice of $a$ roots. Indeed, $\kappa(F_0-Z)\ge(K-14)a\ge2a$,
and $|F_3|>Ka\ge2a$, $|H_0|>4La\ge2a$,
so M provides $2a$ disjoint $F_3$–$H_0$ paths. Section 3.2
combines these with the double fan into $8a$ disjoint paths to
$H_0$: one from each of the $7a$ proxies and $a$ from distinct
vertices of $F_3$. Root a $K_a$ model in $F_3$ at those $a$
vertices. The hub is $4a$-linked by L. In the hub, pair the
$6a$ terminal-proxy path ends as prescribed and pair each root-proxy
path end with one residual-model path end. The disjoint path
families and the rooted model form a proxy $(a,3a)$ woven solution.

To build the rooted model in $F_3$, choose arbitrary distinct
$r'_1,\ldots,r'_a\in F_3$. Since $\delta(F_3)\ge Ka$, choose
$2a$ distinct neighbors $s_j,s_{a+j}$ of $r'_j$ outside the roots.
Delete these $3a$ vertices, obtaining $F_4$. It is an induced
$K_{14a}$-minor-free graph. Use separability on $F_4$, then on
one of the two resulting pieces. This gives three disjoint induced
graphs $J_1,J_2,J_3$, each with

$$\chi(J_i)\ge U+Ba-D_1(a)-2\sigma(a). \tag{4.3}$$

By the second threshold GN supplies induced $Ka$-connected
$J'_i\subseteq J_i$ with six-$Ka$ further color loss. Combining
(4.2)–(4.3), the total loss from $F$ to each child is

$$14a+28a+3a+h(a)+12Ka+2\sigma(a)
  =(45+12K)a+h(a)+2\sigma(a).$$

By (4.1), $\chi(J'_i)\ge U+B(2a/3)$ and $\kappa(J'_i)\ge Ka$.
Write $T=3^m$. The integer scales are $a_i=2^i3^{m-i}$ for
$0\le i\le m$. At $i=m$, $2^m\le3^m/\sqrt{m\log3}$,
because $(3/2)^m>\sqrt{m\log3}$ for $m\ge1$ (check $m=1$,
then compare successive ratios). Thus every nonbase scale has an
integer child $a'=2a/3$. The induction hypothesis gives
$W(a',3a';J'_i)=W(a',2a;J'_i)$ for all three children.

Choose $a'$ distinct target vertices in each child and enumerate
them $t_1,\ldots,t_{2a}$ in three successive blocks of length
$a'$. The graph $F_3-\{r'_1,\ldots,r'_a\}$ has connectivity at
least $(K-1)a\ge2La$, so L supplies disjoint paths
$s_j\leadsto t_j$ for $1\le j\le2a$. Apply Section 3.3
successively to the three children. Its woven definition permits
all $2a$ pairs, and the new linkage meets each rooted child model
exactly at its $a'$ target vertices.

For $j=1,\ldots,a$, take the union of $r'_j$, its two chosen
neighbor edges, paths $j$ and $a+j$, and the child branches at
$t_j$ and $t_{a+j}$. These $a$ unions are disjoint and connected.
Indices $j$ and $a+j$ lie in different blocks because their
difference $a$ exceeds block length $a'=2a/3$. Thus each union
uses two of the three children. Any two two-element subsets of a
three-element set intersect; in a common child, the corresponding
two branches are distinct and adjacent. The unions therefore form
a $K_a$ model rooted at the $r'_j$. This proves the claim. $\square$

The claim is deliberately phrased with explicit contracts. Its proof
does not infer SC or CI from chromatic estimates; those are supplied
only in the respective specializations.


## 5. Corollary 24: explicit specialization

Set

$$K=10000,\quad A=2000,\quad B=10^6(d+1),\quad
 U=AT,\quad h(a)=980a,\quad \sigma(a)=14da.$$

The hub comes from GN alone. Whenever $\chi(X)\ge980a$, delete
vertices until an induced subgraph has chromatic number exactly
$980a=7(140a)$, then apply GN with $r=140a$. The resulting induced
hub has connectivity at least $140a\ge4La=64a$ and chromatic
number at most $980a$.

For nonbase $a$, the separation hypothesis in Corollary 24 is
exactly the second contract of Section 4. The hub input has

$$\chi(F_0-Z)\ge AT+(B-14)a\ge980a.$$

The two GN thresholds and the second separation threshold reduce to

$$AT+(B-1022)a\ge7Ka,$$
$$AT+(B-1025-6K-28d)a\ge7Ka,$$
$$B>1025+6K+42d.$$

These hold for every $d\ge1$. For example the last right side is
$61025+42d$, while $B=10^6(d+1)$. The child budget (4.1) becomes

$$B/3\ge1025+12K+28d=121025+28d,$$

again true for every $d\ge1$. These inequalities also justify the
first separability application, the second one after losing $14da$,
and each GN application. No implicit “sufficiently large” choice is
used here.

At a base scale $a\le T/\sqrt{\log T}$, assume the normalized
graph $F_0$ is $K_{14a}$-minor-free. KT gives

$$\chi(F_0)\le840a\sqrt{\log(14a)}+1
 \le840T\sqrt{1+\frac{\log14}{\log T}}+1
 \le840T\sqrt{1+\frac{\log14}{\log100}}+1<2000T.$$

But $\chi(F_0)\ge AT+(B-7)a\ge2000T$, a contradiction.
Consequently the base condition of Section 4 holds. We have proved
the full assertion of main-paper Lemma 23 from GN, L, KR, KT and M:
every eligible induced $F$ with $\kappa(F)\ge Ka$ and
$\chi(F)\ge AT+Ba$ satisfies $W(a,3a;F)$.

Now suppose $G$ has no $K_t$ minor and satisfies the stated
separability condition. If $\chi(G)\ge(A+B+6K)T$, GN with $r=KT$
gives an induced $KT$-connected $F$ with
$\chi(F)\ge(A+B)T$. The GN hypothesis holds since
$A+B+6K\ge7K$. The just-proved induction at $a=T$ makes $F$
$(T,3T)$-woven, hence gives a $K_T$ minor and therefore a $K_t$
minor. This is impossible. Therefore

$$\chi(G)<(A+B+6K)T=(B+62000)T
 <3(B+62000)t,$$

because the least power of three above $t$ is strictly below $3t$.
This proves Corollary 24 using the self-contained inputs
established below.

## 6. Theorem 4: Delcourt–Postle specialization

We first prove a corrected form of Delcourt–Postle Theorem 7.1.
Fix a power of three $T\ge3$ and define, for a host graph $G$ and
an absolute integer $D$,

$$F_D(G,T)=\max\left(\{0\}\cup
 \left\{\frac{\chi(H)}q:
 \begin{array}{l}
 H\subseteq G,\quad H\text{ has no }K_q\text{ minor},\\
 q\in\mathbb Z,\quad T/\sqrt{\log T}\le q\le14T,\\
 |H|\le Dq(\log q)^4
 \end{array}\right\}\right).$$

Choose $D$ at least $2000$, $C_i$, $28$, and all elementary numerical
constants used in Section 4; enlarging it only strengthens the
hypotheses. Put $f=F_D(G,T)$, $K=D$, $U=DT$, and
$B=276D(1+f)$. Use the **same GN hub as in Section 5**:
$h(a)=980a$. This removes SC from the outer recursion; SC is still
needed upstream to prove CI in Section 7.

At a nonbase scale $a>T/\sqrt{\log T}$, put
$\sigma(a)=14C_i a(1+f)$. If an induced subgraph $Y\subseteq G$
has no $K_{14a}$ minor, then

$$g_{C_i}(Y,14a)\le f.$$

Indeed $14a$ lies in the defining interval of $F_D(G,T)$, and
every candidate for $g_{C_i}$ is a candidate for $F_D$, because
$D\ge C_i$. Thus CI says that every such $Y$ with
$\chi(Y)>2\sigma(a)$ is $\sigma(a)$-chromatic-separable. This
provides both separation calls in the shared recursion.

The GN hub exists because $\chi(F_0-Z)\ge DT+
(276D(1+f)-14)a\ge980a$, and it has
$\kappa(H_0)\ge140a\ge64a=4La$. For the numerical budget,
$C_i\le D$ and $f\ge0$ give

$$\begin{aligned}
(45+12D)a+h(a)+2\sigma(a)
 &=\bigl(1025+12D+28C_i(1+f)\bigr)a\\
 &\le\bigl(1025+40D+28Df\bigr)a\\
 &\le92D(1+f)a
 =Ba/3 .
\end{aligned}$$

The last inequality follows already for $D\ge20$. The residual
chromatic number before the first GN application is at least
$DT+(276D(1+f)-1022)a$, and the three children before their GN
applications each have at least
$DT+(276D(1+f)-1025-6D-28C_i(1+f))a$ colors.
For $D\ge2000$ both quantities exceed $7Da$; the latter also
exceeds $2\sigma(a)$. The first and second separation inputs
exceed $2\sigma(a)$ as well. These elementary checks discharge all
nonbase thresholds of Section 4.

The printed proof of DP Theorem 7.1 invokes DP Lemma 5.13 at
$a\le T/\sqrt{\log T}$ using only $\kappa(G)\ge Da$.
That invocation is invalid: $a\sqrt{\log a}\le T$ gives no lower
bound of the form $\kappa(G)\ge C a\sqrt{\log a}$. Here is a repair
which uses the *same* KT base as Corollary 24. If
$a\le T/\sqrt{\log T}$ and normalized $F_0$ is
$K_{14a}$-minor-free, then

$$\chi(F_0)\le840a\sqrt{\log(14a)}+1
 \le840T\sqrt{1+\frac{\log14}{\log3}}+1
 <1600T.$$

On the other hand $\chi(F_0)\ge DT+(B-7)a\ge DT$.
Since $D\ge2000$, this is impossible. Thus the minor branch
always applies at base scales. Notice that this repair does not
change Theorem 7.1's statement or the order cutoff in Theorem 4.

The shared induction now proves: every induced $F\subseteq G$
with $\kappa(F)\ge Da$ and
$\chi(F)\ge D[T+276a(1+f)]$ satisfies $W(a,3a;F)$.
Taking $F=G$ gives the corrected Theorem 7.1; CI and all
common inputs are proved below.

To deduce Theorem 4, set $C=3^9D=19683D$. Suppose that a
$K_t$-minor-free $G$, $t\ge3$, violates
$\chi(G)\le Ct(1+f_C(G,t))$. Put $f=f_C(G,t)$ and let
$T$ be the least power of three at least $t$; then $t\le T<3t$.
GN with $r=DT$ gives an induced $DT$-connected $F\subseteq G$
and

$$\chi(F)\ge\chi(G)-6DT
 >D\{19683t(1+f)-18t\}.$$

The GN threshold holds because the assumed chromatic number is
much larger than $7DT$.

We claim $F_D(F,T)\le f$. Let $H\subseteq F$ and integer $q$
contribute to $F_D(F,T)$. If $q\le t$, then
$q\ge T/\sqrt{\log T}\ge t/\sqrt{\log t}$: the function
$x/\sqrt{\log x}$ is increasing for $x\ge3$. Also
$|H|\le Dq(\log q)^4\le Cq(\log q)^4$.
Thus the same $H,q$ contribute to $f$. If $q>t$, then $H$
is $K_t$-minor-free because $G$ is; $q\le14T<42t$; and

$$|H|\le D(42t)(\log(42t))^4
 \le19683Dt(\log t)^4=Ct(\log t)^4.$$

For the middle inequality, $\log42/\log t\le
\log42/\log3<7/2$, so
$42(1+7/2)^4<3^9$. Therefore $H,t$ contribute to $f$,
and $\chi(H)/q\le\chi(H)/t\le f$. The claim follows.

Finally, since $T<3t$,

$$\begin{aligned}
\chi(F)
 &>Dt\{19683(1+f)-18\}\\
 &\ge 3Dt(277+276f)\\
 &> DT\{1+276(1+F_D(F,T))\}.
\end{aligned}$$

The middle inequality is immediate after expansion:
$19665+19683f\ge831+828f$. This is the **full** chromatic
hypothesis of corrected Theorem 7.1 at the top scale $a=T$.
The printed DP final proof bounds only a weaker expression that
omits the additive $276$; retaining the original $3^9$ factor
resolves the issue. Applying Theorem 7.1 gives a $K_T$ minor
in $F$, hence a $K_t$ minor in $G$, contradiction. This proves
Theorem 4, since CI and the common inputs are proved below.

## 7. Closing the chromatic-inseparability contract from its inputs

This section derives CI from SC, GN, M, the up-to woven theorem
explained in 7.1, and elementary lemmas proved here. SC and the
common GN, L, KR, KT, and M inputs are proved below; Appendix F
proves the rooted-minor input. The construction
is a corrected version of Delcourt–Postle §§5–6, with the case $T_0=1$ handled
separately. To avoid confusion, $T_0$ denotes the *number of
sequential stages*; $T$ in Sections 4–6 denotes a power-of-three
scale.

### 7.1 Rooted model together with prescribed linkage

The following strengthened woven theorem is what the sequential
proof actually needs.

**Uniform woven theorem.** There is an absolute $C_w$ such that for
$a\ge2$, $b\ge0$,
$\kappa(X)\ge C_w\max\{a\sqrt{\log a},b\}$ implies $W(a,b;X)$.

Here is the derivation from the rooted density theorem proved in
Appendix F. In a prescribed instance, let $\ell\le b$ be the number
of nonsingleton terminal pairs; singleton sites are protected below.
For $(a,\ell)=(2,0)$, delete every singleton site except the two roots.
The remaining graph is connected by the assumed connectivity;
split a path between the roots into adjacent connected branches
and use the protected sites as one-vertex linkage paths.
For every other $a\ge2$ and $0\le\ell\le b$, put
$H=K_a+\ell K_2$, where $+$ denotes disjoint union. Its order
$h=a+2\ell$ is at least three. By KT and induction on $\ell$,
density $c=30a\sqrt{\log a}+2\ell$ forces an $H$ minor:
delete the ends of any edge to reduce density by at most two,
and then use the induction hypothesis; the case $\ell=0$ is KT.
For the density calculation, if an $n$-vertex graph has density
$d=e/n\ge1/2$, deleting the ends of an edge removes at most
$2n-3$ edges, and the new density is at least
$d-2+(2d-1)/(n-2)\ge d-2$. All graphs in this induction
have density far above $1/2$.
Let $U$ contain **all** original roots and terminals, including the
sites of singleton pairs. For each root and each endpoint of a
nonsingleton pair, choose a distinct neighbor outside $U$ as a proxy;
coincident roles receive separate proxies. Delete $U$ and apply
Appendix F to the remaining graph, assigning the proxies to their
corresponding vertices of $H$. To check one uniform constant, put
$M=\max\{a\sqrt{\log a},b\}$. Then
$h\le(2+1/\sqrt{\log2})M<3.21M$,
$|U|\le a+2b<3.21M$, and $c\le32M$.
With $C_w=10^6$, deleting $U$ leaves connectivity at least
$(10^6-3.21)M$, both above $h$ and with half this value
exceeding $12c+5000h<
12\cdot32M+5000\cdot3.21M<16500M$.
The greedy proxy choices are possible because each original
vertex has at least $C_wM$ neighbors and at any stage fewer than
$|U|+h<6.42M$ vertices are forbidden. The $K_a$ branches form
the rooted clique model, while each $K_2$ pair of branches and
its joining edge supplies one disjoint path. Reattach each original
root or nonsingleton terminal to its assigned proxy; add the
protected singleton sites as one-vertex paths. A root that is also
a terminal is then exactly an intended model–linkage overlap.
Since $\ell$ was arbitrary up to $b$, the theorem gives
the *up-to* version directly. This also fixes the printed range
mismatch: DP Lemma 5.11 says $\ell\ge a$, but DP Lemma 5.13
applies it with potentially $\ell<a$.
We also need a knitting corollary. For any $p\ge q\ge1$, there
is an absolute $C_{\rm knit}$ such that
$\kappa(X)\ge C_{\rm knit}p$ lets one connect every partition
of any $p$ specified vertices into at least $q$ parts by
pairwise disjoint connected subgraphs, one containing each part.
To prove it from L, choose a spanning tree on the specified
vertices of each part, making at most $p-1$ edges in total.
Treat those edges as indexed terminal pairs. A terminal may
occur in several pairs. For each occurrence choose a distinct
adjacent proxy outside the original $p$ vertices; minimum
degree at least $3p$ permits the greedy choice. Delete the
original $p$ vertices. If there are no selected pairs, take the
specified singleton vertices as the connected subgraphs.
Otherwise let $\ell$ be the actual number of selected pairs,
so $1\le\ell\le p-1$. If the original connectivity is at
least $33p$, the remaining graph is $32p$-connected and
hence at least $16\ell$-connected; apply L to exactly those
$\ell$ proxy pairs. Attach the original endpoints by their
proxy edges and unite
the paths belonging to each part. Paths of different parts
are disjoint, because their proxies and the original
specified vertices are disjoint. Within one part their
union is connected, since its selected pairs form a
spanning tree. Thus one may take $C_{\rm knit}=33$.
This is DP Theorem 5.8 with a concrete sufficient constant.

### 7.2 Small connected pieces

We derive DP Corollary 6.1 from SC. Let $c=C_s$, let
$L_t=\log t$, $r=\lceil\sqrt{L_t}\rceil$, and $k\ge t$.
Define $g$ by the maximum of $\chi(H)/t$ over
$K_t$-minor-free subgraphs of $X$ with at most
$c^2tL_t^4$ vertices, including zero. Suppose $X$ has
no $K_t$ minor and $\chi(X)\ge4ck(1+g)$.

Take a maximal disjoint family of small $k$-connected
subgraphs, each with at most $c^2tL_t^3$ vertices. If it has
at least $r$ members, we are done. Otherwise its union $J$
has at most $(r-1)c^2tL_t^3\le c^2tL_t^4$ vertices:
$r-1<\sqrt{L_t}\le L_t$, as $t\ge3$. Hence
$\chi(J)\le tg$. By maximality and the contrapositive of SC,
every subgraph of $X-J$ has density below $ck$.
Greedy coloring therefore gives $\chi(X-J)\le2ck+1\le3ck$.
Consequently $\chi(X)\le tg+3ck<4ck(1+g)$, a contradiction.
Thus $r$ such small pieces exist. The citation to DP Theorem
2.2 in their printed proof of Corollary 6.1 should be to 2.3.

We also use a cheap-tree lemma. If $X$ is connected and
$\varnothing\ne S\subseteq V(X)$, there is an induced connected
$Q\subseteq X$ containing $S$ and $S\subseteq S'\subseteq V(Q)$
with $|S'|\le3|S|$ and $\chi(Q-S')\le2$.
Induct on $|S|$. For one terminal use its singleton graph.
For more, remove one terminal $v$ and construct $Q_0,S'_0$
for the rest. If $v\in V(Q_0)$, keep $Q_0$ and add $v$
to $S'_0$. Otherwise take a shortest path from $v$ to
$Q_0$, add that path to $Q_0$, and add to $S'_0$ the path's
two ends and the neighbor of its $Q_0$ end. The path's
remaining interior is induced and has no edge to $Q_0$
by shortestness; it is bipartite. This proves the lemma
(DP Lemma 6.2).

### 7.3 The sequential invariant

Choose an absolute integer $C$ so large that

$$C\ge\max\{24c\,L\,C_{\rm knit}\,C_w,\ 240,\ 12\},
 \qquad C_i=C^2.$$

Increasing $C$ further to absorb the elementary inequalities
below does not alter the theorem. For fixed $t\ge3$, put
$L_t=\log t$, $r=\lceil\sqrt{L_t}\rceil$,
$x=\lceil t/\sqrt{L_t}\rceil$, $k=Ct$,
$g=g_{C_i}(G,t)$, $F=1+g$, and $m=C^2tF$.
The elementary estimates used below are

$$x\le t,\quad (r-1)x\le2t,\quad rx\le3t,\quad
r\le2\sqrt{L_t},\quad
2x\sqrt{\log(2x)}\le4t.$$

For the last estimate, $2\sqrt{L_t}\le t$ for $t\ge3$
(the difference $t-2\sqrt{\log t}$ is positive and
increasing there), so
$x\le t/\sqrt{L_t}+1\le(3/2)t/\sqrt{L_t}$.
Also $x\le t$ and
$\log(2x)\le\log(2t)\le(5/3)L_t$, because
$\log2/\log3<2/3$. Hence
$(2x)^2\log(2x)\le15t^2<16t^2$.
The other estimates follow directly from the ceiling
definitions and $L_t>1$.

Assume $G$ is $K_t$-minor-free,
$m$-chromatic-inseparable, and $\chi(G)\ge2m$.
For each $0\le T_0\le r$ we assert the following *stage
invariant*: with $s=T_0x$, there are a $K_s$ model
$\mathcal A$ with a core $S$, and a $k$-connected subgraph
$H$ such that

$$|S|\le2T_0^2c^2tL_t^3,\qquad
 \chi(H)\ge\chi(G)-m/2,$$

and $H$ is tangent to $\mathcal A$ (each branch meets $H$
in exactly one vertex), with
$V(H)\cap V(\mathcal A)\subseteq S$.
A *core* means that every adjacency between two different
branches has a witnessing edge whose ends both lie in $S$.

At $T_0=0$ the empty model and empty core work; GN with
parameter $k$ supplies $H$ because
$\chi(G)\ge2m\ge7k$, and
$6k\le m/2$. This fills a step the printed proof calls
“trivial” without extracting the required connected graph.

Suppose $1\le T_0\le r$ and the previous invariant has
$\mathcal A'$, $S'$, and $H'$ with $s'=(T_0-1)x$ branches.
Let $w_1,\ldots,w_{s'}$ be their distinct tangent vertices
in $H'$, and delete them from $H'$ to get $H_1$.
Then $\chi(H_1)\ge\chi(G)-m/2-2t\ge4ckF$.
Section 7.2 supplies $T_0$ disjoint $k$-connected subgraphs
$J_1,\ldots,J_{T_0-1},D$ in $H_1$, each of order at most
$c^2tL_t^3$. In each $J_i$, choose $2x$ vertices
$w_{s'+2(i-1)x+1},\ldots,w_{s'+2ix}$.
Put $W_1=\{w_1,\ldots,w_{3s'}\}$.
Here $|W_1|=3s'\le6t$; if $T_0=1$, it is empty.

Because $H'$ is $k$-connected and $k\ge18t\ge3|W_1|$,
the doubled-source Menger argument of Section 3.4 gives two disjoint-outside-source
$W_1$–$D$ paths per source, all with different ends in $D$.
Call this family $\mathcal Q_1$. Shorten its paths to be induced;
their vertex union has chromatic number at most
$4|W_1|\le24t$.
Let $J$ be the union of all $J_i$ and $D$. Its order is at
most $T_0c^2tL_t^3\le C_i tL_t^4$ by the choice of $C$,
so $\chi(G[J])\le tg$. Delete $J$ and all vertices of
$\mathcal Q_1$ from $H'$, obtaining $H_2$ with
$\chi(H_2)\ge\chi(H')-kF\ge7k$.
GN gives a $k$-connected $H_3\subseteq H_2$ with

$$\chi(H_3)\ge\chi(H')-7kF\ge\chi(G)-m.$$

In $H'-W_1$ use Menger to find $2s$ disjoint
$H_3$–$D$ paths, where $s=s'+x$; its connectivity is
at least $k-6t\ge2s$. Call them $\mathcal Q_2$,
and pair their $2s$ distinct $H_3$ ends arbitrarily.
If $T_0\ge2$, identify each pair to a new source vertex
and apply the redundant Menger lemma of Section 3.2 to
$\mathcal Q_1$ and $\mathcal Q_2$. This yields
$b=3s'+s$ disjoint paths $\mathcal P$ to distinct vertices
$u_1,\ldots,u_b\in D$, starting at all $3s'$ members of
$W_1$ and at one chosen member from each of the $s$
$H_3$ pairs. If $T_0=1$, the first source set is empty,
so the printed redundancy lemma does not apply:
simply keep one path from each pair in $\mathcal Q_2$.
Then $b=s=x$. In both cases $\mathcal P$ meets $H_3$
only at its $s$ selected source ends, meets $D$ only at
the $u_j$, and meets the old model only at its previous
tangent vertices.

For each $i<T_0$, the uniform theorem of 7.1 makes
$J_i$ $(2x,b)$-woven: $b\le10t$ and
$2x\sqrt{\log(2x)}\le4t$, while its connectivity is $k=Ct$.
Apply Section 3.3 successively to reroute $\mathcal P$
through $J_i$ and obtain a $K_{2x}$ model
$\mathcal M_i$ rooted at its $2x$ chosen vertices.
The resulting $\mathcal P'$ meets $\mathcal M_i$
exactly at those roots. It remains within
$V(\mathcal P)\cup\bigcup_iV(J_i)$; this is the correct
containment, replacing the false printed assertion
$V(\mathcal P')\subseteq V(\mathcal P)$.
In particular its intersections with $D$, $H_3$,
and the old model are unchanged.

### 7.4 Building the next model and restoring its color reserve

Use the following indices, all between $1$ and $b$:
for $i<T_0$ and $j\le x$, put
$a_{i,j}=s'+2(i-1)x+x+j$; for $j\le s'$ put
$b_j=s'+j+x(\lceil j/x\rceil-1)$ and
$b'_j=3s'+j$. Partition the $u$-vertices into
terminal groups

$$S_j=\{u_j,u_{b_j},u_{b'_j}\}\quad(j\le s'),$$
$$S_{s'+j}=\{u_{a_{i,j}}:i<T_0\}
  \cup\{u_{4s'+j}\}\quad(j\le x).$$

Their indices partition $[b]$: the old groups use the
$s'$ old tangent paths, the first halves of the $J_i$
source paths, and $s'$ new $H_3$ paths; the new groups
use the second halves and the remaining $x$ new
$H_3$ paths.

When $T_0\ge2$, the knitting consequence of 7.1
applied in $D$ to these groups produces disjoint
connected subgraphs $D_1,\ldots,D_s$, with
$S_j\subseteq D_j$. **When $T_0=1$, this is insufficient:**
the groups are singletons, so knitting gives no edges
between the $D_j$. Instead use the uniform woven theorem
with $(a,b)=(x,0)$ in $D$, rooted at
$u_1,\ldots,u_x$. Its connectivity condition follows from
$x\sqrt{\log x}\le2t$ and $C\ge2C_w$.
Let its rooted $K_x$ branches be the $D_j$.
This supplies the missing clique adjacencies at the first
stage of DP Lemma 6.4.

For each old index $j\le s'$, form a new branch from
the old branch $A'_j$, paths
$P'_j,P'_{b_j},P'_{b'_j}$, $D_j$,
and the branch of $\mathcal M_{\lceil j/x\rceil}$
rooted at $w_{b_j}$. For each new $j\le x$,
form a branch from $P'_{4s'+j}$, $D_{s'+j}$,
and, for every $i<T_0$, $P'_{a_{i,j}}$ and its
root branch in $\mathcal M_i$.
These branches are disjoint and connected because the
path indices partition $[b]$ and rerouting makes the child
models meet paths only at their assigned targets.
Old–old adjacency comes from $\mathcal A'$.
Old–new adjacency comes from the appropriate $\mathcal M_i$.
New–new adjacency comes from any $\mathcal M_i$ when
$T_0\ge2$, or from the rooted model in $D$ when $T_0=1$.
They form a $K_s$ model $\mathcal A''$, tangent to
$H_3$ at the $s$ chosen $H_3$ starts.

Set $S=S'\cup J\cup\{\text{these }s\text{ tangent vertices}\}$.
All edges witnessing adjacency of $\mathcal A''$ lie in
$S$: old–old edges were in $S'$, while new adjacencies
are inside $J$. Thus $S$ is a core, and the estimates
$s\le3t$, $T_0\le2\sqrt{L_t}$ give
$|S|\le2T_0^2c^2tL_t^3$.
First replace each branch $A''_j$ by its induced closure
$G[V(A''_j)]$; its vertex set, disjointness, tangency,
and witnessing adjacency edges are unchanged. Apply the
cheap-tree lemma within that induced graph to the nonempty
terminal set $S\cap V(A''_j)$ (it contains the tangent vertex).
Retain an induced connected subbranch $A_j$ containing
those terminals and a set $X_j$ of at most three times
their number such that $\chi(A_j-X_j)\le2$.
The core edges and tangent vertex survive, so
$\mathcal A=\{A_j:j\le s\}$ remains a $K_s$ model
with core $S$, still tangent to $H_3$.
Let $A=\bigcup_jV(A_j)$ and $X=\bigcup_jX_j$.
Distinct palettes on different branches give
$\chi(G[A-X])\le2s\le6t$, while
$|X|\le3|S|\le C_i tL_t^4$.
Since $G$ has no $K_t$ minor, the definition of $g$
gives $\chi(G[X])\le tg$, and therefore
$\chi(G[A])\le6t+tg\le kF$.

Delete $A$ from $G$, producing $H_4$ with
$\chi(H_4)\ge\chi(G)-kF\ge7k$. GN gives a
$k$-connected $H_5\subseteq H_4$ with
$\chi(H_5)\ge\chi(G)-m/2$.
If $|V(H_5)\cap V(H_3)|<k$, delete this
intersection from $H_5$. The remainder has
chromatic number at least $\chi(G)-m$, as does $H_3$,
and the two are disjoint, contradicting
$m$-chromatic-inseparability.
Otherwise $H=H_3\cup H_5$ is $k$-connected:
after deleting fewer than $k$ vertices, both
$H_3$ and $H_5$ remain connected and still meet.
It has the required chromatic number and remains
tangent to $\mathcal A$, because $H_5$ avoids $A$.
This completes the stage induction.

At $T_0=r$, the model has order $rx\ge t$,
contradicting $K_t$-minor-freeness. Therefore
the assumed chromatic-inseparability is impossible.
This proves CI with $C_i=C^2$ using SC
and the woven theorem established in Section 7.1. The printed proof's
last line says “follows from Lemma 2.5”;
the induction just proved is Lemma 6.4.

## 8. The small connected subgraph theorem from its inputs

This section derives SC from the Norin–Postle
unbalanced bipartite edge bound, KT, and Mader's density-to-connectivity
lemma. Appendix C proves the bipartite bound from KT, and
Appendix A.4 proves the needed Mader form. Put $c_0=6400$.
The bipartite statement is that,
for every bipartite $K_t$-minor-free graph with parts $P,Q$,

$$e(P,Q)\le c_0t\sqrt{\log t}\sqrt{|P||Q|}
 +(t-2)(|P|+|Q|). \tag{8.1}$$

Mader's statement in the density convention $d(X)=e(X)/|X|$
is that $X$ has a subgraph of connectivity at least $d(X)/2$.
We use it only when $d(X)/2$ is at least a prescribed integer.

First prove a trimming lemma. Let $r>2$, $\delta>0$, and
$S\subseteq V(X)$ satisfy

$$(r-2)e(X[S])>(r-1)\delta|S|+e_X(S,V(X)-S). \tag{8.2}$$

Then there is nonempty $S'\subseteq S$ with minimum degree
in $X[S']$ at least $\delta$ and
$|N_X(v)\cap S'|\ge\deg_X(v)/r$ for all $v\in S'$.
Choose an inclusion-minimal set satisfying (8.2).
If some $v$ has internal degree $z<\delta$, removing it
reduces the left side by $(r-2)z$, reduces the vertex term
by $(r-1)\delta$, and increases the boundary term by at most
$z$; hence (8.2) still holds, contradiction. If some
$v$ has internal degree $z<\deg(v)/r$, removing it changes
the boundary by $2z-\deg(v)$. The difference between
the left and right sides changes by
$-(r-2)z-[2z-\deg(v)]+(r-1)\delta
 =\deg(v)-rz+(r-1)\delta>0$.
Again (8.2) survives, contradiction. This proves the lemma.

Now let $t\ge3$ and $k\ge t$ be integers, and let $G$ have no $K_t$ minor
and density at least $d=C_sk$, where $C_s=480c_0$.
Delete surplus edges so its density is exactly $d$; the
edge count $d|G|$ is integral since $C_s,k$ are integers.
KT gives $d<30t\sqrt{\log t}$, so
$k\le t\sqrt{\log t}$. Write $L_t=\log t$ and

$$h=\left\lceil10L_t^2(t/k)^2\right\rceil.$$

Take a maximal family of disjoint nonempty connected
subgraphs $H_1,\ldots,H_m$ of order exactly $h$ such that
contracting each to one vertex loses at most
$(d/10)$ times the total number of vertices contracted
away. Let $G'$ be the result and let $X=\{x_1,\ldots,x_m\}$
be the new contraction vertices. Then $G'$ is
$K_t$-minor-free and
$e(G')\ge(9/10)e(G)$. Also

$$|X|\le\frac{|G|}{10L_t^2}(k/t)^2. \tag{8.3}$$

Partition the remaining vertices of $G'$ as follows:
$Y$ consists of vertices with at least $d/20$ neighbors
in $X$; $Z$ consists of vertices outside $X\cup Y$
with degree at least $20dL_t$; and $S$ consists of all
other vertices. Put $T_*=X\cup Y\cup Z$.
We claim

$$|Y|\le L_t|X|(t/k)^2. \tag{8.4}$$

If $|Y|\le|X|$, this follows from
$k\le t\sqrt{L_t}$. Otherwise apply (8.1) to the
bipartite graph between $X$ and $Y$. Its edge count
is at least $(d/20)|Y|\ge3c_0k|Y|$.
The additive term in (8.1) is at most
$2c_0k|Y|$, since $k\ge t$ and $|X|<|Y|$.
Subtracting and squaring gives (8.4).

The degree sum gives $|Z|\le|G|/(10L_t)$.
Since $L_t(t/k)^2\ge1$, (8.3) and (8.4) imply

$$|T_*|\le\frac{3|G|}{10L_t}. \tag{8.5}$$

Apply (8.1) to the bipartite graph between $S$ and $T_*$.
Using (8.5), $|S|\le|G|$, and $|G'|\le|G|$ gives

$$e_{G'}(S,T_*)\le c_0(2t-2)|G|.$$

KT applied to $G'[T_*]$ gives
$e(G'[T_*])<30t\sqrt{L_t}|T_*|\le9t|G|$.
As $d=480c_0k\ge480c_0t$, the sum of these two
edge counts is strictly below $e(G)/20$. Hence

$$e(G'[S])>
 \frac{9}{10}e(G)-\frac1{20}e(G)
 =\frac{17}{20}d|G|.$$

With $r=3$ and $\delta=2d/5$, the right side of
(8.2) is at most $(4d/5)|G|+e_{G'}(S,T_*)$,
which is below $(17d/20)|G|$. The trimming lemma
therefore gives a nonempty $S'\subseteq S$ satisfying

$$\delta(G'[S'])\ge2d/5,\qquad
 |N_{G'}(v)\cap S'|\ge\deg_{G'}(v)/3
 \quad(v\in S'). \tag{8.6}$$

Choose a nonempty connected $H\subseteq G'[S']$,
of order at most $h$, such that contracting $H$
loses at most $(d/10)(|H|-1)$ edges, and subject
to this choose $H$ of maximum order. A singleton
qualifies. If $|H|=h$, then $H$ (all its vertices
are uncontracted originals) can be added to the
family $H_1,\ldots,H_m$ while maintaining the
aggregate contraction-loss inequality. This
contradicts maximality of $m$. Thus $|H|\le h-1$.

Let $G''$ result from contracting $H$ to a vertex $x$,
let $\Delta=e(G')-e(G'')$, put
$R=N_{G''}(x)-X$, and put
$R'=N_{G''}(x)\cap S'$.
Each internal edge of $H$ and each duplicated edge
to a common neighbor contributes to $\Delta$.
Counting all incidences from $H$ to $S'$ therefore gives

$$|R'|\ge\sum_{v\in H}|N_{G'}(v)\cap S'|-2\Delta.$$

By (8.6), the sum is at least $(2d/5)|H|$;
by choice of $H$, $2\Delta\le(d/5)|H|$.
Consequently

$$|R'|\ge\frac12\sum_{v\in H}|N_{G'}(v)\cap S'|
 \ge\frac16\sum_{v\in H}\deg_{G'}(v)
 \ge|R|/6. \tag{8.7}$$

Fix $v\in R'$. It is adjacent to $x$, so
$H\cup\{v\}$ is connected and has at most $h$
vertices. By maximality of $H$, contracting
this enlarged set incurs more than
$(d/10)|H|$ edge loss. The first contraction
incurred at most $(d/10)(|H|-1)$ loss, so
the additional contraction of edge $vx$
loses more than $d/10$ edges. Since $d/10$
is an integer, at least $d/10$ vertices are
common neighbors of $v$ and $x$ in $G''$
(the edge $vx$ accounts for one further loss).
By definition of $S$, $v$ has fewer than
$d/20$ neighbors in $X$, so at least
$d/20$ of these common neighbors lie in $R$.
As $R'\subseteq R$, counting edges inside $R$
and using (8.7) gives

$$e(G[R])\ge\frac{d}{40}|R'|
 \ge\frac{d}{240}|R|.$$

Thus $d(G[R])\ge d/240=2c_0k\ge2k$.
Mader's lemma produces a $k$-connected
subgraph inside $G[R]$.

Finally every vertex of $H\subseteq S$ has degree
below $20dL_t$, so

$$|R|\le20dL_t|H|
 <200dL_t^3(t/k)^2
 =200C_s(t^2/k)L_t^3
 \le C_s^2tL_t^3,$$

using $k\ge t$ and $C_s\ge200$.
The resulting $k$-connected subgraph has the
order bound required in SC. Taking its induced
closure preserves both properties.

This completes the deduction of SC from Appendix C,
Appendix A.4, and the KT proof in Appendix E.

## 9. Dependency ledger and source repairs

The proof dependencies are

$$\begin{array}{c}
 \text{Corollary 24}\leftarrow
 \text{shared induction}\leftarrow
 \{\mathrm{GN,L,KR,KT,M}\};\\[1mm]
 \text{Theorem 4}\leftarrow
 \text{shared induction}+\mathrm{CI}
 \leftarrow\mathrm{SC}+\text{uniform woven theorem}
 \leftarrow\{\mathrm{NP,KT,rooted\ density,GN,L,KR,Mader,M}\}.
\end{array}$$

GN, M, and the needed Mader form are proved in Appendix A; KR
in Appendix B; NP in Appendix C; L in Appendix D; KT in
Appendix E; and the rooted density theorem in Appendix F.
Thus there is no external mathematical proof leaf.
The printed Delcourt–Postle proof requires the following corrections
for the deduction above to be literally valid. They are *not*
additional hypotheses of the endpoint theorems.

* Its Theorem 7.1 base case does not meet its cited Lemma 5.13's
  connectivity condition. Section 6 uses the common KT base instead.
* Its Lemma 5.15 applies exactly-$b$ wovenness to fewer than $b$
  paths. Section 1 uses up-to-$b$ wovenness; Section 3.3 then
  proves rerouting with the needed containment.
* Its Lemma 5.11 states $\ell\ge a$ whereas its Lemma 5.13
  invokes it also for $\ell<a$. Section 7.1 derives the
  all-parameter form from Appendix F.
* Its Lemma 6.4 at stage $T_0=1$ gets no clique edges
  among the new branches from its knitting theorem, and the
  stated redundancy lemma has an empty source set there.
  Section 7.4 supplies a rooted model in $D$, and Section 7.3
  takes one path from each pair without redundancy.
* Its Claim 6.4.1 states the rerouted paths stay inside the
  original paths. They may use vertices of the woven children;
  the correct containment is in the union of those two sets.
* In the final proof of Theorem 1.6, the displayed chromatic
  bound at the top scale omits the additive $276$. Section 6
  retains the original $3^9$ factor and verifies the full
  inequality. The displayed logarithmic inequality on that
  page has a missing fourth power; Section 6 gives the
  corrected inequality.
* The proof of its Corollary 6.1 cites Theorem 2.2 instead of
  the needed Theorem 2.3, and its proof of Lemma 2.5 cites
  itself instead of Lemma 6.4. Section 7 uses the intended
  statements.

**Conclusion on status.** Sections 3–8 and Appendices A–F give
a standalone mathematical proof of both endpoint statements.
This document is a blueprint for formalization, not a Lean proof:
none of these two endpoint theorems is claimed to be checked
without implementing the arguments in Lean.
## Appendix A. Elementary and connectivity proofs

### A.1 Set Menger theorem

Here is a direct finite max-flow proof of M, included to make the
path bookkeeping independent of an unstated version of Menger.
For each vertex $v$ replace it by an arc $v_{\rm in}\to
v_{\rm out}$ of capacity one. For each original edge $uv$, add
arcs $u_{\rm out}\to v_{\rm in}$ and
$v_{\rm out}\to u_{\rm in}$ of capacity $N+1$, where $N=|V(X)|$.
Connect a new source to every $a_{\rm in}$, $a\in A$, and
every $b_{\rm out}$, $b\in B$, to a new sink, again with
capacity $N+1$. If $A$ and $B$ overlap, a vertex in their
intersection supports a one-vertex path and has its own capacity-one
arc; this construction handles it without special treatment.

All capacities are integers. Starting with zero flow, repeatedly
augment one unit along a source–sink path in the residual network.
The process terminates because the total flow is at most $N$.
At termination, let $R$ be the vertices reachable from the source
by residual arcs. Every original arc from $R$ to its complement
is saturated, and every reverse arc across the cut carries zero
net residual capacity, so the value of the flow equals the capacity
of this cut. Thus the maximum flow equals the minimum cut.
There is always a cut of capacity at most $|A|\le N$, namely
the split arcs for $A$, so a minimum cut uses no capacity-$N+1$
arc. It is exactly a set of split arcs, hence a set of original
vertices separating $A$ from $B$. Conversely every vertex
separator gives such a cut after taking the source-reachable
vertices of the graph with its split arcs removed. Finally an
integral flow decomposes into source–sink paths and cycles;
discard cycles. Capacity one on split arcs makes the resulting
paths vertex-disjoint. On each path, retain the subpath from its
last vertex of $A$ to its first subsequent vertex of $B$;
this has no other $A\cup B$ vertices. This proves M, including the
possibility that a separator contains terminals.

We repeatedly use the following minimum-cut saturation consequence.
If $S$ is a minimum $A$–$B$ separator of order $m$, then M
provides $m$ disjoint $A$–$B$ paths. Each meets a distinct
vertex of $S$. Taking their tails after their last visits to
$S$ gives disjoint paths from all of $S$ into $B$. When $S$
is the adhesion of a separation, these tails lie on its $B$ side:
returning to the opposite strict side would require another visit
to $S$. The same argument works if a path has length zero.

### A.2 Additive Girão–Narayanan theorem

We give an adaptation of the template argument in
[Girão–Narayanan](https://arxiv.org/pdf/2004.00533), because their
displayed Theorem 1.1 states a weaker result while the additive
form GN is used quantitatively here.

Let $k\ge1$, $q=\chi(G)\ge7k$, and let $\mathcal C$ be a palette
of $q-1$ colors. On an induced graph $J$, a *template*
$(S,c,F)$ consists of a properly precolored set $S$ and a
forbidden-color set $F(v)\subseteq\mathcal C$ at every
$v\in V(J)-S$. Its degree is

$$d(S,c,F)=k|S|+\sum_{v\notin S}|F(v)|.$$

Call it admissible if its degree is at most $2k^2$ and
each forbidden set has size at most $2k$. It is obstructing
if no proper $\mathcal C$-coloring of $J$ extends $c$ while
avoiding all forbidden sets. The empty template obstructs $G$,
as $q=\chi(G)$. Choose an induced vertex-minimal graph $H$
that has an admissible obstructing template; among such
templates on $H$, choose one maximizing $|S|$. In particular
$|S|\le2k$, and every proper induced subgraph of $H$ is
extensible for *every* admissible template.

Every $v\notin S$ has $|F(v)|\le k-1$. Otherwise choose a color
$\gamma$ outside $F(v)\cup c(S)$; this is possible since
$|\mathcal C|\ge7k-1>4k\ge|F(v)|+|S|$.
Precolor $v$ with $\gamma$ and remove its forbidden list.
Obstruction persists, and the degree changes by
$k-|F(v)|\le0$, contradicting maximality of $|S|$.

We claim $\kappa(H)\ge k$. If $|H|\le k$, then every
unprecolored vertex has at least
$(q-1)-2k-(k-1)=q-3k\ge4k\ge|H-S|$
available colors outside $c(S)$ and its forbidden set.
Color all vertices of $H-S$ with distinct available colors,
a contradiction. Thus $|H|>k$.

Suppose a separator $X$ of size at most $k-1$ leaves two
nonempty anticomplete parts $Y,Z$. Restricting the template's
degree to $Y$ and $Z$, one of them has degree at most $k^2$;
call it $Z$. On the proper induced subgraph $H[X\cup Y]$,
keep the original template, and additionally forbid at each
unprecolored $x\in X$ every color used by a precolored
neighbor in $S\cap Z$. There are at most $|S\cap Z|\le k$
such colors, so each list has size at most $(k-1)+k\le2k$.
The degree stays at most $2k^2$: removing $S\cap Z$
saves $k|S\cap Z|$, while the extra forbiddances cost
at most $|X||S\cap Z|\le k|S\cap Z|$. This template
therefore extends to a proper coloring $c'$ of $H[X\cup Y]$.

On the proper induced subgraph $H[X\cup Z]$, keep the original
template on $Z$ and precolor all of $X$ according to $c'$.
This precoloring is proper, including edges from $X$ to
$S\cap Z$, by the added forbidden colors in the first
extension. Its degree is at most
$k|X|+d(\text{template restricted to }Z)
 \le k(k-1)+k^2\le2k^2$; the remaining forbidden lists
have size at most $k-1$. Hence it too extends. The two
colorings agree on $X$, and no edge joins $Y$ to $Z$.
Gluing them colors $H$ contrary to obstruction. This proves
$\kappa(H)\ge k$.

Finally assume $\chi(H)\le q-6k-1$. Properly color $H-S$
with $m\le q-6k-1$ colors. Within each independent
color class, partition vertices into successive chunks:
keep adding vertices until the total number of their
forbidden colors first exceeds $k$, then close the chunk.
Each heavy chunk has weight between $k+1$ and $2k-1$,
because every individual list has size at most $k-1$;
each class has at most one remaining light chunk. Total
forbidden weight is at most $2k^2$, so there are at most
$2k$ heavy chunks. Thus the number $N$ of chunks is at most
$m+2k\le q-4k-1$. A chunk is independent and has total
forbidden weight at most $2k$. It therefore has at least
$|\mathcal C|-|S|-2k\ge q-4k-1\ge N$
colors avoiding the precolored colors and all its forbidden
lists. Give the chunks pairwise distinct such colors, one
chunk at a time. This colors $H$ and respects the template,
a final contradiction. Therefore $\chi(H)\ge q-6k$,
proving GN.

### A.4 The needed density-to-connectivity lemma

We prove the precise form used in Section 8: if $d(X)=e(X)/|X|\ge2k$
for an integer $k\ge1$, then $X$ has a $k$-connected subgraph.
For $k=1$, an edge suffices. Let $k\ge2$ and put $q=2k-3$.
We prove a stronger finite induction: every graph on $n\ge2k-1$
vertices with at least

$$q(n-k+1)+1 \tag{A.1}$$

edges has a $k$-connected subgraph. At $n=2k-1$, the right
side equals $\binom{n}{2}$; the graph is complete and
therefore contains $K_{k+1}$.

For $n\ge2k$, if some vertex has degree at most $q$, delete it;
(A.1) still holds for the smaller graph, so induction applies.
Otherwise the minimum degree is at least $2k-2$.
If the graph is $k$-connected we are done. If not, write its
vertex set as $A\cup B$, with both $A-B$ and $B-A$ nonempty,
no edges between those exclusive parts, and
$|A\cap B|\le k-1$. Every vertex in $A-B$ has all neighbors
in $A$, so $|A|\ge2k-1$; likewise $|B|\ge2k-1$.
If neither induced subgraph on $A$ or $B$ meets (A.1),
induction's contraposition bounds their edge counts by
$q(|A|-k+1)$ and $q(|B|-k+1)$.
Since $|A|+|B|=n+|A\cap B|\le n+k-1$,

$$e(X)\le e(X[A])+e(X[B])
 \le q(n-k+1),$$

contradicting (A.1). Thus one part satisfies the induction
hypothesis and contains the required connected subgraph.

Finally, $d(X)\ge2k$ implies $e(X)\ge2k|X|$ and
$|X|>4k$, so (A.1) holds with ample slack. This proves
the needed form of Mader's lemma without an external input.
### A.3 A few consequences used without separate labels

If $\chi(X)\ge m$ for an integer $m$, vertex deletion one at
a time yields an induced subgraph of chromatic number exactly
$m$: deleting one vertex changes chromatic number by at most
one. Hence GN yields an $r$-connected induced hub of chromatic
number at most $7r$ whenever $\chi(X)\ge7r$.

An $m$-vertex-critical subgraph $C$ of an $m$-chromatic graph
has minimum degree at least $m-1$, hence
$e(C)/|C|\ge(m-1)/2$. Applying KT to this particular
subgraph gives the coloring consequence stated in Section 2.
If $X$ has minimum degree at least $k$, then its density
is at least $k/2$. These facts account for all conversions
between chromatic number, minimum degree, and density made
in the outer proof.

## Appendix B. Rooted clique minors from ordinary clique minors

We prove KR from M. The argument is an explicit separator
dichotomy adapted from the mechanism of
[Dujmović et al., Lemma 12](https://link.springer.com/article/10.1007/s00493-025-00168-w).
For a specified $r$-set $R$, write $G^{+R}$ for the graph
obtained by adding all missing edges inside $R$. An
*$R$-attached $K_r$ model in $G-R$* has $r$ disjoint
connected branches, pairwise adjacent by actual edges of
$G$, and a bijection assigning to each branch a distinct
root in $R$ adjacent to that branch.

**Separator dichotomy.** Let $R$ be an $r$-set and let
$\mathcal B=(B_1,\ldots,B_{2r})$ be a $K_{2r}$ model in
$G^{+R}$. Then either

1. $G-R$ has an $R$-attached $K_r$ model; or
2. $G$ has a separation $(A,B)$ of order below $r$ with
   $R\subseteq A$ and an entire original branch
   $B_j\subseteq B-A$.

Here a separation has $A\cup B=V(G)$ and no edge between
$A-B$ and $B-A$. We prove the dichotomy by induction on
$|G|$. Suppose neither alternative holds. If some branch
$U$ has more than one vertex and is not contained in $R$,
choose an edge $uv$ in its connected spanning subgraph
with $u\notin R$. This is an actual edge of $G$, since
only edges with both ends in $R$ were added. Contract it
to $c$, retaining $c$ as the root represented by $v$
if $v\in R$. The given model becomes a $K_{2r}$ model
in the completed contracted graph.

Apply induction there. An attached model lifts through
the contraction: when its branch uses $c$ as a nonroot,
replace $c$ by the edge $uv$; when $c$ represents a root,
an attachment using $u$ is made into an attachment to
the original root $v$ by adding $u$ to that branch.
Thus the contracted graph has the separator alternative.
Pull its separation back to $G$. Its order is at most
$r$; if $c$ lies on the boundary, replace it there by
both $u,v$. It still has $R$ on the near side and some
original branch on the strict far side. Since alternative
2 fails in $G$, the pulled-back order is exactly $r$,
and both $u,v$ lie in its boundary $X=A\cap B$.
As $u\notin R$ and $|X|=|R|=r$, some root lies in
$A-B$; hence $B$ is a proper smaller graph.

There are $r$ vertex-disjoint $R$–$X$ paths in $G[A]$.
If not, M supplies a separator of order below $r$
between them inside $A$. Every path from $R$ to the
original branch strictly beyond $X$ must first traverse
$X$, so that smaller separator, together with the
far side $B$, gives alternative 2 in $G$. Because the $r$ disjoint paths use all $r$ vertices of
each endpoint set, none can contain another vertex of
$R\cup X$ internally; a vertex in $R\cap X$ has a
trivial path.

Every branch of $\mathcal B$ meets $B$: the branch
lying in $B-A$ is adjacent to every other branch,
and no edge joins $A-B$ to $B-A$. Restrict each branch
to $B$ and complete $X$ to a clique. On a path joining
two vertices of a restricted branch, each excursion
through $A-B$ has both ends in $X$, so an added $X$
edge replaces it. For adjacency of two restricted
branches, a witnessing edge with both ends in $B$
survives. If a witnessing edge has an end in $A-B$,
then each of its branches meets $X$ by connectedness
and because both branches meet $B$; the completed $X$
clique supplies their adjacency. The same reasoning
covers an added edge within $R$, since $R\subseteq A$.
Thus the restrictions form a $K_{2r}$ model in
$G[B]^{+X}$; disjointness is preserved because the
original branches were disjoint.

Apply induction to the proper smaller pair $(G[B],X)$.
If it gives an $X$-attached $K_r$ model in $B-X$,
extend its branches along the disjoint $R$–$X$ paths
in $A$, omitting each original root from the branch.
The paths have no internal $R\cup X$ vertices, and
$A-B$ is disjoint from the model, so this is an
$R$-attached model in $G-R$, alternative 1.
If instead it gives a separation of order below $r$
placing $X$ on the near side and a restricted branch
strictly on the far side, glue the whole $A$ to that
near side. The corresponding original branch cannot
visit $A-B$: since it is connected and meets $B$,
such a visit would force it to meet $X$, contrary
to its restriction lying strictly beyond the new
separator. The glued separation gives alternative 2
in $G$. Both outcomes contradict our assumption.

We have shown that every branch of $\mathcal B$ is
either a singleton or contained in $R$. At most $r$
branches meet $R$, so at least $r$ singleton branches
avoid $R$. Let $M_0$ be their vertex set. M gives
$r$ disjoint $R$–$M_0$ paths: a smaller separator
would leave one of these $r$ singleton branches
strictly beyond it and give alternative 2. Trim each
path at its first hit of $M_0$. Their distinct ends
are distinct singleton branches, pairwise adjacent
by actual $G$ edges because they avoid $R$.
Enlarge these singleton branches along the trimmed
paths, excluding the original roots. This is an
$R$-attached $K_r$ model, alternative 1, the final
contradiction. The dichotomy follows.

Now let $G$ be $r$-connected, have a $K_{2r}$ minor,
and let $R$ be any $r$ distinct vertices. The model
also exists in $G^{+R}$. The separator alternative
is impossible: deleting fewer than $r$ boundary
vertices would leave a root on the near side and
an original clique branch on the far side, with no
connecting path. Hence the attached alternative
holds. Add each assigned root and its attachment
edge to its branch. The resulting model is rooted
at $R$, proving KR.

## Appendix C. The unbalanced bipartite minor bound

We prove (8.1) with $c_0=6400$, using only KT. This is a
quantitative reconstruction of [Norin–Postle,
Theorem 3.2](https://arxiv.org/pdf/2004.10367); the auxiliary
lemma below makes the rounding explicit.

**Near-complete auxiliary lemma.** Let $t\ge3$,
$n\ge9t$, $\ell=\lfloor n/(9t)\rfloor$, and let $J$ be
an $n$-vertex graph with missing-edge fraction
$q=1-e(J)/\binom n2$. If

$$6t(100q)^{\ell^2}\le1, \tag{C.1}$$

then $J$ has a $K_t$ minor. If $q=0$, this is immediate.
Otherwise choose $Z\subseteq V(J)$ of size
$z=\lfloor n/3\rfloor$ such that every vertex in $Z$
has at most $2qn$ non-neighbors. Such a set exists:
the average number of non-neighbors is
$q(n-1)<qn$, so Markov gives at least $n/2$
suitable vertices. The elementary bounds
$z-1\ge n/4$ and $z-\ell\ge n/4$ hold for
$n\ge9t\ge27$.

For a uniform $\ell$-set $X\subseteq Z$, a fixed
$v\in Z-X$ has no neighbor in $X$ with probability
at most $(8q)^\ell$ (expose a random $\ell$-set in
$Z-\{v\}$). Thus the expected number of such $v$
is at most $n(8q)^\ell$. Call $X$ *good* if this
number is at most $3n(8q)^\ell$. Markov gives
$\Pr(X\text{ good})\ge2/3$. Conditional on a good
$X$, a uniform $\ell$-set $Y\subseteq Z-X$ has
no edge to $X$ with probability at most

$$\left(\frac{3n(8q)^\ell}{z-\ell}\right)^\ell
 \le 12^\ell(8q)^{\ell^2}
 \le(100q)^{\ell^2}. \tag{C.2}$$

Choose uniformly $3t$ mutually disjoint $\ell$-sets
$X_1,\ldots,X_{2t},Y_1,\ldots,Y_t$ in $Z$.
This is possible since $3t\ell\le z$. Each $X_i$
is a uniform $\ell$-set and, conditional on it,
each $Y_j$ is uniform in $Z-X_i$. Equations (C.1)
and (C.2), with the union bound, show that
$X_i$ is good and has an edge to every $Y_j$
with probability at least
$2/3-t(100q)^{\ell^2}\ge1/2$. The expected
number of such $X_i$ is at least $t$; fix an
outcome with at least $t$ and retain exactly $t$.

Condition (C.1) implies $q\le1/100$.
Two vertices of $Z$ have more than $z$ common
neighbors outside $Z$: at least
$n-z-4qn>z$ of the outside vertices work.
For each retained $i$, fix an anchor in $X_i$.
Connect every other vertex of $X_i\cup Y_i$
to this anchor by a distinct common neighbor
outside $Z$. These connectors can be chosen
greedily and globally distinctly, because fewer
than $2t\ell\le z$ are needed. This makes $t$
disjoint connected branch sets. They are pairwise
adjacent, since every retained $X_i$ has an edge
to every $Y_j$. The auxiliary lemma follows.

Now suppose (8.1) fails, and choose a
counterexample $G=(A,B)$ with as few vertices
as possible. Write $a=|A|\ge b=|B|\ge1$,
$\alpha=\sqrt{a/b}\ge1$, $\tau=t\sqrt{\log t}$,
and $C=6400$. Thus

$$e(G)>C\tau\sqrt{ab}+(t-2)(a+b). \tag{C.3}$$

Deleting one vertex and applying minimality gives

$$\deg(v)>\frac{C\tau}{2\alpha}+t-2
 \quad(v\in A),\qquad
\deg(u)>\frac C2\alpha\tau+t-2
 \quad(u\in B). \tag{C.4}$$

Indeed, the decrement of $\sqrt{ab}$ upon
deleting an $A$-vertex is at least $1/(2\alpha)$,
and the decrement upon deleting a $B$-vertex
is at least $\alpha/2$.

KT gives $e(G)/(a+b)<30\tau$. Since $a\ge b$,
there is $v_0\in A$ with
$\deg(v_0)\le e(G)/a<60\tau
 \le(C/4)\alpha\tau$. For two distinct neighbors
$u_1,u_2\in B$ of $v_0$, contract the
$u_1v_0u_2$ path and then delete any loops
and same-side edges, obtaining a bipartite
$K_t$-minor-free graph with part sizes
$a-1,b-1$. Such a neighbor pair exists by
(C.4). If
$m_{12}=|N(u_1)\cap N(u_2)-\{v_0\}|$,
the contraction loses exactly
$\deg(v_0)+m_{12}$ edges. Minimality,
(C.3), and
$\sqrt{ab}-\sqrt{(a-1)(b-1)}\ge\alpha/2$
therefore give

$$m_{12}\ge s:=\frac C4\alpha\tau. \tag{C.5}$$

(The strict inequalities in fact give a little more.)

Choose $n=\lceil\tau/\alpha+t-2\rceil$
neighbors $X$ of $v_0$, possible by (C.4).
We have $n\ge t-1$ and
$n\le\tau/\alpha+t-1\le2\tau$.
Delete any vertex of $A-\{v_0\}$ without
a neighbor in $X$. Independently for each
remaining vertex $w\in A-\{v_0\}$, choose
uniformly one neighbor in $X$ and contract
$w$ onto it. The resulting random graph
$H$ has vertex set $X$, and is a minor of
$G$. For each pair $x,y\in X$, every one
of their at least $s$ common neighbors
outside $v_0$ makes $xy$ an edge with
probability at least $2/n$, independently.
Thus

$$\Pr(xy\notin E(H))\le
 q_0:=\exp(-2s/n). \tag{C.6}$$

If $\binom n2q_0<1$, some realization of
$H$ is complete. Adjoining $v_0$ gives a
$K_{n+1}$ minor, hence a $K_t$ minor,
a contradiction. Otherwise $n^2q_0\ge1$.
Taking logarithms yields $n\log n\ge s$
and consequently

$$n^2\log n\ge sn
 \ge (C/4)t^2\log t. \tag{C.7}$$

If $n<20t$, the left side is less than
$400t^2\log(20t)$, which is at most
$400(1+\log20)t^2\log t$
because $\log t\ge1$. This is strictly below
$(C/4)t^2\log t$, as
$C/4=1600>400(1+\log20)$.
Hence $n\ge20t$.

Choose an outcome of $H$ whose actual
missing-edge fraction $q_H$ is at most
$q_0$; such an outcome exists by (C.6)
and averaging. Since $n\le2\tau$ and
$\alpha\ge1$, (C.5) gives $2s/n\ge
C/4=1600$, so $q_0<10^{-4}$.
With $\ell=\lfloor n/(9t)\rfloor$,
we have
$\ell\ge n/(18t)\ge\sqrt{\log t}/(18\alpha)$.
Therefore

$$(100q_H)^{\ell^2}
 \le(100q_0)^{\ell^2}
 \le q_0^{\ell^2/2}
 =\exp(-s\ell^2/n)
 \le\exp(-s\ell/(18t))
 \le t^{-C/1296}
 \le t^{-3}
 \le\frac1{6t}, \tag{C.8}$$

where the last inequality uses $t\ge3$.
The near-complete auxiliary lemma applies to
$H$ and gives a $K_t$ minor, the final
contradiction. This proves (8.1) with
$c_0=6400$.
## Appendix D. Quantitative linkedness

We prove L, namely that every $16k$-connected graph is
$k$-linked. The argument is a self-contained reconstruction
of [Thomas–Wollan, §§2–3](https://thomas.math.gatech.edu/PAP/klink.pdf),
with slack in the constants. All uses of Menger refer to
Appendix A.1.

For a vertex set $U$, put
$\rho_G(U)=|\{e\in E(G):e\cap U\ne\varnothing\}|$.
Fix $k\ge1$ and $\lambda=8k$. A pair $(G,X)$ with
$|X|\le2k$ is *$\lambda$-massed* if

* $\rho_G(V(G)-X)>\lambda|V(G)-X|$; and
* every separation $(A,B)$ with $X\subseteq A$ and
  $|A\cap B|<|X|$ satisfies
  $\rho_G(B-A)\le\lambda|B-A|$.

Call $(G,X)$ *linked* if every pairing of any even
subset of $X$ has vertex-disjoint paths joining its
pairs, all with interiors outside $X$. A separation
$(A,B)$ is *rigid* if $X\subseteq A$, $B-A\ne\varnothing$,
and $(G[B],A\cap B)$ is linked.

We first show that every $\lambda$-massed pair is
linked. Suppose not; choose a nonlinked pair $(G,X)$
with $|X|\le2k$, first minimizing $|G|$, then
minimizing $\rho_G(V-X)$, then maximizing $e(G[X])$.
In particular $|X|\ge2$.

**No rigid separation.** We prove that $(G,X)$
has no rigid separation of order at most $|X|$.
First suppose $(A,B)$ is rigid of order below
$|X|$, choosing one with $A$ inclusion-minimal.
Put $S=A\cap B$ and $H=G[A]+K_S$. If $(H,X)$
were linked, take a linkage in $H$. On each path,
shortcut between its first and last vertices of
$S$, leaving at most one artificial $S$-edge,
and replace all artificial edges by a disjoint
linkage in $(G[B],S)$. This would link $(G,X)$.
Thus $(H,X)$ is nonlinked. Its first mass
condition holds because the second mass condition
for $(G,X)$ gives

$$\rho_H(V(H)-X)
 \ge \rho_G(V(G)-X)-\rho_G(B-A)
 >\lambda(|V(G)-X|-|B-A|)
 =\lambda|V(H)-X|. \tag{D.1}$$

By minimality of $|G|$, $(H,X)$ fails the
second mass condition. Choose a violating
separation $(A',B')$ of $H$ with $B'$
inclusion-minimal, and put $T=A'\cap B'$.
Then $(H[B'],T)$ is $\lambda$-massed.
Its first condition is the violating density.
If its second condition failed at a separation
$(C,D)$, then $(A'\cup C,D)$ would be another
violating separation of $H$ with strictly smaller
far side, a contradiction. Since $|H[B']|<|G|$,
$(H[B'],T)$ is linked.

As $S$ is a clique in $H$, no separation of $H$
can put one vertex of $S$ on each strict side.
Hence either $S\subseteq A'$ or $S\subseteq B'$.
In the former case, $(A'\cup B,B')$ is a separation
of $G$ of order $|T|<|X|$ with the same dense
far shore; the artificial $S$-edges do not meet
that shore. This violates the mass condition
of $(G,X)$. In the latter case, the linked
pair $(H[B'],T)$ expands through the linked
pair $(G[B],S)$, by replacing artificial
$S$-edges as above. Thus
$(G[B'\cup B],T)$ is linked and
$(A',B'\cup B)$ is a rigid separation of
$G$ of order $|T|<|X|$. Its near side
$A'$ is strictly smaller than $A$, a contradiction.

Now suppose $(A,B)$ is rigid of order exactly
$|X|$, and put $S=A\cap B$. If $G[A]$ has
$|X|$ disjoint $X$–$S$ paths, they transfer
every pairing of $X$ to the linked pair
$(G[B],S)$, so $(G,X)$ is linked. Otherwise
Menger gives an $X$–$S$ separation
$(A',B')$ in $G[A]$ of minimum order
$q<|X|$, with $X\subseteq A'$ and
$S\subseteq B'$. Put $T=A'\cap B'$.
A maximum family of $q$ disjoint $X$–$S$
paths uses all of $T$; their suffixes give
$q$ disjoint $T$–$S$ paths in $G[B']$.
They transfer any pairing of $T$ to
$(G[B],S)$, so $(G[B'\cup B],T)$ is linked.
Then $(A',B'\cup B)$ is a rigid separation
of order $q<|X|$, already excluded.
This proves the assertion.

**Common neighbors.** Fix a pairing of
some vertices of $X$ that cannot be linked.
Every nonedge of $G[X]$ is one of its paired
edges: adding any other root edge leaves both
mass conditions unchanged, preserves
nonlinkability of this pairing, and contradicts
the third extremal choice. Thus each
$x\in X$ has at most one nonneighbor in $X$.

Every vertex outside $X$ has an incident edge.
Otherwise deleting an isolated outside vertex
preserves both mass conditions and nonlinkability,
contradicting minimal $|G|$.

For an edge $uv$ with $v\notin X$, contract
$uv$ to $w$, retaining the name of $u$ if
$u\in X$, and call the graph $H$. Any
linkage of $(H,X)$ lifts through the
contraction, so $H$ is nonlinked.
We claim it still satisfies the second
mass condition. Otherwise choose a
violating separation $(A,B)$ of $H$ with
$B$ inclusion-minimal, and put $T=A\cap B$.
Exactly as in the previous paragraph,
$(H[B],T)$ is $\lambda$-massed and
hence linked by graph-order minimality.
There are three positions for $w$.

If $w\notin B$, put both $u,v$ on the near
side. The same dense far shore violates
the mass condition of $G$, because splitting
a contracted vertex cannot decrease the
number of edges incident with that shore.
If $w\in B-A$, put both $u,v$ on the far
side. The $T$-linkage in $H[B]$ lifts
through the contraction, giving a rigid
separation of $G$ of order $|T|<|X|$.
If $w\in T$, put both $u,v$ on both sides.
The resulting $G$-separation $(A^*,B^*)$
has adhesion
$T^*=(T-\{w\})\cup\{u,v\}$, of order
$|T|+1\le|X|$. Its far shore is still
dense. Moreover $(G[B^*],T^*)$ is
$\lambda$-massed: a violation of its
second condition would extend to a
violation of the second condition of
$(G,X)$, of order below $|T^*|\le|X|$.
Some root lies outside $B$ because
$|T|<|X|$; therefore $|B^*|<|G|$.
Minimality makes $(G[B^*],T^*)$ linked,
giving a forbidden rigid separation.
This proves the claim.

The contracted $H$ is nonlinked and
satisfies its second mass condition, so
it fails the first. Let
$c(u,v)=|N_G(u)\cap N_G(v)|$.
If both endpoints lie outside $X$,
contraction decreases $\rho(V-X)$
by $1+c(u,v)$. If $u\in X$ and
$v\notin X$, it decreases by
$1+c(u,v)+\varepsilon$, where
$\varepsilon$ counts neighbors of
$v$ in $X$ not adjacent to $u$.
Our root-edge observation gives
$0\le\varepsilon\le1$. Contraction
reduces $|V-X|$ by one, so the strict
first mass condition in $G$ and its
failure in $H$ imply that the decrease
in $\rho$ is at least $\lambda+1$.
Consequently

$$c(u,v)\ge\lambda-1
 \quad\text{for every edge }uv
 \text{ meeting }V(G)-X. \tag{D.2}$$

**An edge-tight small core.** For such
an edge $e=uv$, $G-e$ remains nonlinked.
It still satisfies the second mass
condition. Indeed, any newly violating
separation must place $u,v$ on opposite
strict sides. Every common neighbor of
$u,v$ then lies in its adhesion, which
would have order at least
$\lambda-1\ge|X|$, impossible.
Thus $G-e$ fails the first mass
condition, by minimality of
$\rho_G(V-X)$. Since $e$ meets
$V-X$ and $\lambda$ is integral,

$$\rho_G(V-X)=\lambda|V-X|+1. \tag{D.3}$$

Put $f(x)=|N_G(x)-X|$ for $x\in X$.
Each $f(x)\ge1$: otherwise
$(X,V(G)-\{x\})$ is a separation
of order $|X|-1$ whose far shore
is $V-X$ and is too dense.
For a neighbor $v\notin X$ of
$x$, at most $|X|-1$ of their
common neighbors lie in $X$.
By (D.2),

$$f(x)\ge1+(\lambda-1)-(|X|-1)
 =\lambda-|X|+1\ge6k+1. \tag{D.4}$$

Every outside vertex has degree at
least $\lambda$ by (D.2).
Let $\delta_*$ be the least such
degree. If $\delta_*\ge2\lambda$,
then (D.4) and $|X|\ge2$ give

$$2\rho_G(V-X)
 =\sum_{v\notin X}\deg_G(v)
  +\sum_{x\in X}f(x)
 >2\lambda|V-X|+2,$$

contrary to (D.3). Hence
$\lambda\le\delta_*<2\lambda$.
Choose an outside vertex $v$ of
degree $\delta_*$. Its induced
closed neighborhood
$L=G[N_G[v]]$ has
$|L|=\delta_*+1\le2\lambda=16k$
and minimum degree at least
$\lambda=8k$: each neighbor
of $v$ has the edge to $v$
and at least $\lambda-1$
common neighbors with $v$,
all lying in $L$.

We need the following small-core fact:
if $|L|\le16k$ and
$\delta(L)\ge8k$, then $L$
contains a $k$-linked subgraph.
Suppose not. In particular $L$
is not $k$-linked. Choose $k$
disjoint prescribed terminal pairs
with no full linkage. Among
collections of mutually disjoint
paths of length at most seven
for some of the prescribed pairs,
with interiors avoiding all
terminals, first maximize the
number $p$ of paths and then
minimize their total length.
Let $U$ contain all $2k$
terminals and every vertex of
these $p$ paths. Since $p\le k-1$,

$$|U|\le2k+6p\le8k-6. \tag{D.5}$$

Any vertex outside $U$ has at
most three neighbors on one
completed path: four would
allow a shortcut through that
vertex, decreasing the total
length. It has at most one
neighbor at each unmatched
terminal. Thus every vertex
of $R=L-U$ has at most
$3p+2(k-p)\le3k$ neighbors
in $U$, and

$$\delta(R)\ge5k,\qquad
 |R|\le14k. \tag{D.6}$$

Choose an unmatched pair $s,t$.
Each has a neighbor in $R$ by
(D.5) and $\delta(L)\ge8k$.
Let $S$ be the vertices of $R$
at distance at most two from
$N_R(s)$, and define $T$
similarly from $N_R(t)$.
These sets are nonempty,
disjoint, and anticomplete:
an intersection or an edge
between them would give an
$s$–$t$ path of length at
most seven in $R$, increasing
$p$. They cover $R$. Indeed,
if $z\in R-(S\cup T)$, choose
$x\in N_R(s)$ and
$y\in N_R(t)$. The three
open neighborhoods
$N_R(z),N_R(x),N_R(y)$
are pairwise disjoint, each
of size at least $5k$,
contradicting $|R|\le14k$.
Thus $R$ has at least two
components. Its smallest
component $J$ has
$|J|\le7k$ and
$\delta(J)\ge5k$.

For completeness, a graph $Q$
on at least $2k$ vertices with

$$2\delta(Q)\ge|Q|+3k-4 \tag{D.7}$$

is $k$-linked. Given $k$ terminal
pairs, use an edge for an adjacent
pair. For a nonadjacent pair,
the two vertices have at least
$2\delta(Q)-|Q|-2k+4\ge k$
common neighbors outside the
terminal set. Choose a distinct
middle vertex greedily for
each such pair. Applying (D.7)
to $J$, since
$10k\ge7k+3k-4$,
shows that $J$ is $k$-linked,
the contradiction proving the
small-core fact.

Finally, let $J$ be this
$k$-linked subgraph of $G$.
If there are $|X|$ disjoint
$X$–$J$ paths, trim them at
their first visits to $J$.
To route a pairing of an even
subset of $X$, pair the unused
arrival vertices among themselves,
adding one fresh vertex of $J$
if their number is odd, then pad
to $k$ pairs with fresh vertices
of $J$. The resulting $k$-linkage
in $J$ avoids every unused arrival;
discard its dummy paths and attach
the selected fan paths. This
contradicts nonlinkability.
Otherwise Menger gives a
minimum $X$–$J$ separation
$(A,B)$ of order $q<|X|$.
Its adhesion $T=A\cap B$
has $q$ disjoint $T$–$J$
paths in $G[B]$ by the
minimum-cut saturation
argument used above.
They route every pairing of
$T$ through $J$, so
$(G[B],T)$ is linked.
Since $|J|\ge2k>|T|$,
$B-A\ne\varnothing$.
This is a forbidden rigid
separation. We conclude that
every $\lambda$-massed pair
with at most $2k$ roots is linked.

To derive L, let $G$ be
$16k$-connected and let $X$
be any $2k$-set. The minimum
degree bound gives
$e(G)\ge8k|G|$, so

$$\rho_G(V-X)
 =e(G)-e(G[X])
 \ge8k|G|-\binom{2k}{2}
 >8k(|G|-2k).$$

No separation of order below
$2k$ has a nonempty far shore,
so the second mass condition
holds. The established pair
theorem links every pairing
of $X$. Since $X$ was arbitrary,
$G$ is $k$-linked, as claimed.
## Appendix E. The explicit clique-minor density bound

We prove KT with its stated coefficient $30$:

> For every integer $r\ge2$, density
> $e(G)/|G|\ge30r\sqrt{\log r}$ forces a
> $K_r$ minor.

This is a fully quantified version of the
[Alon–Krivelevich–Sudakov short argument](https://www.tau.ac.il/~nogaa/PDFS/minorshort3.pdf).
We include a finite-range induction because the
published short argument is asymptotic.

First, a common reduction. Let $d$ be a positive integer
and suppose $e(G)\ge d|G|$. Among minors with that property
choose $G_0$ minimizing $|G_0|+e(G_0)$. Edge deletion gives
$e(G_0)=d|G_0|$. There are no isolated vertices: deleting
one would preserve the density inequality. Contracting an
edge $uv$ removes exactly
$1+|N(u)\cap N(v)|$ edges, so minimality gives

$$|N(u)\cap N(v)|\ge d
 \qquad(uv\in E(G_0)). \tag{E.1}$$

Choose a vertex $v$ of degree at most $2d$ and put
$H=G_0[N(v)]$. It has at most $2d$ vertices and
minimum degree at least $d$, by (E.1).

For $3\le r\le12$, density $2^{r-3}$
already forces a $K_r$ minor. Induct on $r$.
For $r=3$, $e(G)\ge|G|$ gives a cycle,
which contracts to a triangle. For $r\ge4$,
apply the reduction with $d=2^{r-3}$.
The neighborhood $H$ has density at least
$d/2=2^{(r-1)-3}$, so induction gives a
$K_{r-1}$ minor in $H$. Add $v$ as a
singleton branch adjacent to every
branch of that model. Finally,

$$2^{r-3}\le30r\sqrt{\log r}
 \qquad(3\le r\le12). \tag{E.2}$$

Indeed $2^{x-3}/(x\sqrt{\log x})$ increases for
$x\ge3$: its logarithmic derivative is
$\log2-1/x-1/(2x\log x)>0$ there.
At $r=12$, $512<360\sqrt{\log12}$
because $\log12>9/4$. The case $r=2$
is immediate: the assumed positive
density gives an edge.

Now let $r\ge13$, put $L=\log r$,
$s=\lceil4\sqrt L\rceil$, and
$d=\lfloor30r\sqrt L\rfloor$.
The density hypothesis gives $e(G)\ge d|G|$.
Apply the reduction, obtaining $H$ with
$|H|\le2d$, $\delta(H)\ge d$.
We extract an induced $F\subseteq H$
with $\kappa(F)\ge d/3$ and one of
the correlated pairs of bounds

$$(\mathrm I)\quad |F|\le2d,\ \delta(F)\ge d;
 \qquad
 (\mathrm{II})\quad |F|\le d,\ \delta(F)>2d/3.
 \tag{E.3}$$

If $H$ is already $d/3$-connected,
take $F=H$. Otherwise let $S$ be
a separator of order below $d/3$
and let $A$ be a smallest component
of $H-S$. Then $|A|\le(|H|-|S|)/2\le d$
and $\delta(H[A])\ge d-|S|>2d/3$.
Every two vertices of $A$ have more
than $2(2d/3)-d=d/3$ common neighbors
in $A$. Thus deletion of fewer than
$d/3$ vertices leaves $H[A]$
connected, so $F=H[A]$ satisfies (II).

The branch-set budget is

$$s+8\le4\sqrt L+9
 \le10\sqrt L-\frac1{3r}
 \le\frac d{3r}. \tag{E.4}$$

For the middle inequality, $r\ge13$
gives $L>\frac52$, and hence
$6\sqrt L>6\sqrt{5/2}>9+1/39$.
The last inequality follows from
the floor defining $d$.

Build $r$ disjoint connected branch
sets $Q_1,\ldots,Q_r$ in $F$ in order,
each of size at most $s+8$, making
each new one adjacent to all its
predecessors. Before a step let
$b$ vertices have been used, and
put $F_i=F-\bigcup_{j<i}Q_j$.
By (E.4), $b<d/3$, so $F_i$ is
connected. Write $m_0=|F|$,
$\delta_0=d$ in case (I) and
$\delta_0=2d/3$ in case (II),
and $m=m_0-b$. Then
$\delta(F_i)\ge\delta_0-b$ and
$\delta(F_i)/m>2/5$. Indeed case (I)
gives at least $(d-b)/(2d-b)>2/5$,
and case (II) at least
$(2d/3-b)/(d-b)>1/2$.
It follows that $F_i$ has diameter
at most five: a shortest path of
length six would have vertices
at positions $0,3,6$ with pairwise
disjoint open neighborhoods, each
of size greater than $2m/5$.

Put $m_*=m_0-d/3$ and
$\theta=4m_*e^{-2s/5}$. We claim
that a uniformly random $s$-set
$B\subseteq V(F_i)$ has at most
$\theta$ vertices with no neighbor
in $B$ with probability at least
$3/4$. The expected number is at most

$$m\exp\!\left[-s\frac{\delta_0-b}{m}\right]
 =m\exp\!\left[-s
  \frac{\delta_0-m_0+m}{m}\right]. \tag{E.5}$$

As a function of $m\in[m_*,m_0]$,
the logarithmic derivative of (E.5)
is $(m-s(m_0-\delta_0))/m^2$.
Thus its maximum is at an endpoint.
At $m=m_*$, (E.5) is at most
$m_*e^{-2s/5}$ by (E.3).
At $m=m_0$, the same bound follows
as follows. In case (I),
$m_0/m_*\le3/2$ and
$\delta_0/m_0\ge1/2$, while
$(3/2)e^{-s/2}\le e^{-2s/5}$
for $s\ge7$. In case (II),
$m_0/m_*\le2$ and
$\delta_0/m_0\ge2/3$, while
$2e^{-2s/3}\le e^{-2s/5}$.
Markov proves the claim.

Expose the random $s$-set in random
order. Each component of $F_i[B]$
has a first sampled vertex with no
earlier sampled neighbor. For a vertex
sampled at position $j$, that event
has probability at most
$(1-\delta(F_i)/(m-1))^{j-1}$.
Summing the geometric series gives

$$\mathbb E[\#\mathrm{components}(F_i[B])]
 <\frac{m-1}{\delta(F_i)}<5/2. \tag{E.6}$$

Consequently the probability of
at least four components is below $5/8$.

For each previous branch $Q_j$,
let $A_j$ be the vertices still
available that have no neighbor
in $Q_j$; at its creation it had
size at most $\theta$, and it
only shrinks thereafter. As
$m\ge m_*$, for every such $A_j$,

$$\Pr(B\subseteq A_j)
 \le(\theta/m)^s
 \le(4e^{-2s/5})^s.$$

The probability of this event
for some $j<i$ is below $1/8$.
Indeed, writing $x=\sqrt L>3/2$
and using $s\ge4x$, the fact
that $y\log4-2y^2/5$ decreases
for $y\ge6$ gives

$$\log\!\left[
 r(4e^{-2s/5})^s\right]
 \le-\frac{27}{5}x^2+4(\log4)x
 \le-\frac{27}{5}x^2+\frac{28}{5}x
 \le-\frac{15}{4}<-\log8. \tag{E.7}$$

Together the three failure
probabilities are strictly below
$1/4+5/8+1/8=1$.
Choose $B$ for which none occurs.
It has at most three components,
at most $\theta$ undominated
vertices, and contains a vertex
outside each old $A_j$.

Connect its at most three components
by at most two shortest paths in
$F_i$. Since $\operatorname{diam}(F_i)\le5$,
this adds at most $2(5-1)=8$
vertices. The resulting connected
$Q_i$ has size at most $s+8$.
Define $A_i$ among the still
available vertices to be those
with no neighbor in $Q_i$; it
has size at most $\theta$.
As $B$ is not contained in any
old $A_j$, $Q_i$ is adjacent to
every old $Q_j$. Repeat for all
$r$ steps. The $Q_i$ form a
$K_r$ model, proving KT.
## Appendix F. Rooted minors at high density

We prove the rooted-minor input needed in Section 7.1.
The structural argument reconstructs
[Wollan, §§2–5](https://webdoc.sub.gwdg.de/ebook/serien/e/hbm/hbm302.pdf);
its numerical part uses larger rational constants and
Appendix D in place of a separate edge-density
linkedness theorem.

**Rooted density theorem.** Let $H$ be any graph with
$h=|H|\ge3$, and let $c>1$ be such that every nonempty graph
$J$ with $e(J)\ge c|J|$ contains an $H$ minor.
If $G$ is $h$-connected and
$e(G)/|G|\ge12c+5000h$, then, for every
ordered $h$-set $X$ and every bijection
$\pi:X\to V(H)$, $G$ contains a $\pi$-rooted
$H$ minor.

We prove a stronger statement for massed pairs.
For $U\subseteq V(F)$ write
$\rho_F(U)=|\{e\in E(F):e\cap U\ne\varnothing\}|$.
A pair $(F,R)$ is *$\alpha$-massed* if

$$\rho_F(V(F)-R)>\alpha|V(F)-R| \tag{F.1}$$

and, for each separation $(A,B)$ with $R\subseteq A$
and $|A\cap B|<|R|$,

$$\rho_F(B-A)\le\alpha|B-A|. \tag{F.2}$$

If $Z\subseteq V(F)$ has $|Z|\le h$, say that
$(F,Z)$ is *$H$-universal at $Z$* if for
every injection $\phi:Z\to V(H)$ it has
a $\phi$-rooted model of $H[\phi(Z)]$.
A graph is *$H$-universal* if it has at least $h$ vertices
and this property holds at every $h$-set of its vertices.
A separation $(A,B)$ of $(F,R)$ is
*$H$-rigid* if $B-A\ne\varnothing$,
$|A\cap B|\le h$, and $(F[B],A\cap B)$
is $H$-universal at $A\cap B$.

Put $\alpha=12c+5000h$. We claim every
$\alpha$-massed pair $(G,X)$ with
$|X|\le h$ is $H$-universal at $X$.
Suppose not and choose a counterexample
$(G,X,\pi)$, first minimizing $|G|$
and then $\rho_G(V(G)-X)$ across all
root sets and injections. Set $k=|X|$.
For $k=0,1$, the required empty or
single-vertex model is immediate.
For $k=2$, an edgeless induced target
uses two singleton branches. If its
two labels are adjacent and their roots
$x,y$ lie in one component, split an
$x$–$y$ path into two adjacent connected
rooted branches. If the roots lie in
distinct components, apply (F.2) with
order zero to each root-free component
and with order one to each component
containing one root. The first gives
$e(C)\le\alpha|C|$; the second gives
$e(C)\le\alpha(|C|-1)$, because every
edge of that component meets $C-\{x\}$
or $C-\{y\}$. Summing gives
$\rho_G(V-\{x,y\})\le\alpha(|G|-2)$,
contradicting (F.1). Hence $k\ge3$.

We use three structural facts, proved next.

**(F.a) A minimal massed counterexample has no
$H$-rigid separation.**

**(F.b) If $uv$ is an edge not wholly within $X$,
then contracting it can destroy only (F.1).
If $u,v\notin X$, they have at least
$\lfloor\alpha\rfloor$ common neighbors.
If $u\in X$, $v\notin X$, and
$r=|N(v)\cap(X-\{u\})|$, then they have
at least $\lfloor\alpha\rfloor-r$
common neighbors outside $X$. Moreover
some vertex outside $X$ has degree at
most $2\alpha$.**

**(F.c) $G$ has no $H$-universal subgraph.**

Here and below a rooted model for a target
with zero vertices is the empty family.

### F.1 The structural facts

We first record a standard dense-shore observation.
If $(C,D)$ violates (F.2) in a graph $F$
with root set $R$, choose it with $D$
inclusion-minimal among all violations
and put $T=C\cap D$. Then $(F[D],T)$
is $\alpha$-massed. Its (F.1) is the
strict inequality for $D-C$, since
no edge meeting $D-C$ exits $D$.
If (F.2) failed within $F[D]$ at
$(P,Q)$, then $(C\cup P,Q)$ would
be a separation of $F$ of order
$|P\cap Q|<|T|<|R|$ with the same
dense far shore $Q-P$ and $Q$
properly contained in $D$. This
contradicts minimality of $D$.

We need a finite matching device. For a
bipartite graph with left set $U$ and
right set $W$, there is a matching
whose edges are colored $1$ or $2$
such that each $u\in U$ either is
incident with a color-$2$ matched
edge, or every neighbor of $u$
is incident with a color-$1$
matched edge. Prove this by induction
on $|U|$. An isolated left vertex
satisfies the second condition
vacuously, so delete it. If a
matching covers $U$, color every
matched edge $2$. Otherwise choose
an inclusion-minimal Hall-deficient
set $B\subseteq U$,
$|N(B)|<|B|$. There is a matching
covering $N(B)$ into $B$: if not,
Hall's condition on the right
would yield $J\subseteq N(B)$
with $|N_B(J)|<|J|$, making
$B-N_B(J)$ a smaller deficient
left set. Color this matching $1$,
and recurse on the graph induced
by $(U-B)\cup(W-N(B))$. Vertices
of $B$ have all neighbors
covered in color $1$, while each
other left vertex inherits its
recursive condition and any
additional neighbor in $N(B)$
is also covered in color $1$.
Hall's theorem itself follows from
the integral max-flow proof in
Appendix A.1: use unit arcs
source-to-left and right-to-sink
and capacity $|U|+1$ on each
bipartite edge; a cut below
$|U|$ produces a left set with
fewer neighbors.

We next prove *rigid truncation*.
Suppose $(A,B)$ is $H$-rigid in
$(G,X)$, put $Z=A\cap B$, and let
$K=G[A]+K_Z$. For every injection
$\pi:X\to V(H)$, $(G,X)$ has a
$\pi$-rooted $H[\pi(X)]$ model
if and only if $(K,X)$ does.
For the forward direction, intersect
each branch with $A$. Every excursion
through $B-A$ between two boundary
vertices is replaced by a $Z$-clique
edge; any witnessing edge outside
$A$ implies both branches meet $Z$,
so the clique restores adjacency.
Roots lie in $A$, hence all branches
remain nonempty.

For the reverse direction, choose a
$\pi$-rooted model $(S_i)_{i\in\pi(X)}$
in $K$ minimizing the total number
of vertices in its branches. In
each branch meeting $Z$, choose the
first boundary vertex $v_i$ on a
path from its root, and then a
spanning tree $T_i$ that contains
that root-to-$v_i$ path and whose
edges within $Z$ form a star
centered at $v_i$. This is possible
because $Z$ is a clique in $K$.
Deleting the star edges cuts
$T_i$ into the center subtree
$T(v_i)$ and a hanging subtree
$T(z)$ at each other boundary
vertex $z\in S_i\cap Z$. The
root lies in $T(v_i)$. Each resulting tree component
contains exactly one vertex of $Z$, so it uses no artificial
$Z$-clique edge and is connected in the original $G[A]$.
Each hanging $T(z)$ has an edge to
some branch $S_j$ with
$S_j\cap Z=\varnothing$ and
$ij\in E(H)$: otherwise
discarding $T(z)$ keeps $S_i$
connected and every required
adjacency to a boundary-touching
branch is restored by the
completed $Z$ clique, contrary
to minimality.

Make a bipartite graph between
the hanging vertices $z$ and
the possible labels $j$ just
described. Apply the colored
matching device. Define an
injection $\phi:Z\to V(H)$:
map each center $v_i$ to $i$,
each matched hanging $z$ to
its matched label $j$, and
all remaining boundary vertices
to distinct unused labels.
Matched labels come from
boundary-free branches, so
they do not coincide with
center labels; matching makes
them distinct from each other.
Because $|Z|\le h$, the
assignment extends to all of
$Z$. Rigidity gives a
$\phi$-rooted model
$(U_j)_{j\in\phi(Z)}$ of
$H[\phi(Z)]$ in $G[B]$. Since every vertex of $Z$
has a label, each $U_j$ contains exactly its assigned vertex of
$Z$ and no other boundary vertex.

We construct branches in $G$.
For each boundary-touching
$S_i$, begin with
$T(v_i)\cup U_i$. For each
hanging $z$ matched in color
$2$ to label $j$, add
$T(z)\cup U_j$ to this
$i$ branch. For each
boundary-free $S_j$, retain
$S_j$; if some hanging $z$
is matched in color $1$
to $j$, add $U_j$ and
the path in $T(z)$ from
$z$ to its original
witnessing edge into $S_j$.
Unmatched hanging subtrees
are discarded. The matching
makes these branch sets
disjoint. They are connected:
a color-$2$ piece is joined
to its center through an
$U_i$–$U_j$ edge, since
$ij\in E(H)$; a color-$1$
piece is joined by its
witnessing edge into $S_j$.
Each root stays in its
center subtree or original
boundary-free branch.

All required branch adjacencies
survive. Edges between two
boundary-free branches stay.
Edges between two branches
meeting $Z$ are supplied by
their $U$ branches. For an
edge between boundary-touching
$S_i$ and boundary-free $S_j$,
a witness in $T(v_i)$ or in
a color-$2$ hanging subtree
survives. Otherwise its
hanging vertex $z$ is
unmatched or color-$1$ matched.
The cover property says every
neighbor label of $z$,
including $j$, is color-$1$
matched to some hanging vertex.
Then the new $j$ branch
contains $U_j$ and the new
$i$ branch contains $U_i$;
their edge in the rigid-side
model restores adjacency.
This completes rigid truncation.

To prove (F.a), suppose a rigid
$(A,B)$ exists and choose it
with $|A|$ minimum. Put $Z=A\cap B$.
If $|Z|\ge k$, $k$ disjoint
$X$–$Z$ paths in $G[A]$
would attach to the rigid-side
rooted model, contradicting
the chosen counterexample.
If no such paths exist, a
minimum $X$–$Z$ separator
of order below $k$ gives
a smaller rigid separation:
the minimum-cut saturation
form of Menger supplies
disjoint paths from its
boundary to distinct
vertices of $Z$, through
which every prescribed
root assignment transfers.
Thus $|Z|<k$.

Let $K=G[A]+K_Z$.
The mass condition (F.1)
holds for $(K,X)$:
subtract the at-most
$\alpha|B-A|$ edges
meeting $B-A$, supplied
by (F.2) in $G$, from
the strict global count;
the added $Z$ edges help.
If $(K,X)$ violated (F.2),
take a violating $(C,D)$
with minimal $D$ and
put $T=C\cap D$. The
dense-shore observation
makes $(K[D],T)$
$\alpha$-massed, so
minimality of $|G|$
makes it $H$-universal
at $T$. The clique $Z$
lies entirely in $C$
or entirely in $D$.
If $Z\subseteq C$,
$(C\cup B,D)$ lifts
to a violation of (F.2)
in $G$: no added $Z$
edge meets its far shore.
Thus $Z\subseteq D$.
Rigid truncation transfers
universality of $(K[D],T)$
through the rigid $B$ side
to $(G[B\cup D],T)$.
Hence $(C,B\cup D)$ is
an $H$-rigid separation
with $|C|<|A|$,
contradiction. Therefore
$(K,X)$ is massed.
It is smaller than $G$,
so it has the prescribed
rooted model by minimality.
Rigid truncation lifts it
to $G$, contradiction.
This proves (F.a).

For (F.b), contract an edge
$uv$ not wholly in $X$
to $w$, retaining any root
name, and call the result
$G'$. A rooted model in
$G'$ lifts through the
contraction, so $G'$ remains
a counterexample. We show
it satisfies (F.2).
If not, take a violating
$(C,D)$ with $D$ minimal
and $T=C\cap D$. The
dense-shore observation
makes $(G'[D],T)$ massed,
so by graph-order
minimality it is
$H$-universal at $T$.
If $w\notin D$, lifting
the separation to $G$
gives an (F.2) violation.
If $w\in D-C$, lift
both endpoints into
the far side: the
universal models lift
through $uv$, giving
an $H$-rigid separation
of order $|T|<k$ in $G$.
If $w\in T$, put both
$u,v$ on both sides.
The lifted order is
$|T|+1\le k$. If it
is below $k$, its
unchanged far shore
violates (F.2) in $G$.
If it is exactly $k$,
the lifted far-side
pair is itself
$\alpha$-massed: (F.1)
is the strict density
of its far shore, and
any internal (F.2)
violation splices to
an order-below-$k$
violation in $G$.
Some root lies outside
$D$, because $|T|<k$;
therefore this lifted
far-side graph has
fewer vertices than
$G$. It is universal
by minimality, giving
another forbidden rigid
separation. Hence $G'$
satisfies (F.2), and
must fail (F.1).

Contraction decreases the
number of outside-root
vertices by one. Let
$m=|G-X|$ and
$\rho=\rho_G(V-X)$.
Then $\rho>\alpha m$
but $\rho'\le\alpha(m-1)$,
so the loss in the
integer $\rho$ is at
least $\lfloor\alpha\rfloor+1$.
If $u,v\notin X$ the
loss is $1+|N(u)\cap N(v)|$.
If $u\in X,v\notin X$,
put $r=|N(v)\cap(X-\{u\})|$;
the loss is
$1+r+|N(u)\cap N(v)-X|$.
These give the two
common-neighbor bounds
in (F.b).

Deleting any edge not
wholly in $X$ lowers
$\rho$ by one, preserves
the counterexample,
and cannot preserve
both mass conditions
by extremality. It
cannot break (F.2):
a newly violating
separation must have
the deleted edge
crossing its strict
sides. If both ends
are outside $X$,
their at least
$\lfloor\alpha\rfloor$
common neighbors lie
in its adhesion. If
one end is a root,
the at least
$\lfloor\alpha\rfloor-r$
outside-root common
neighbors and the
$r$ other root
neighbors of its
outside endpoint are
distinct vertices
of the adhesion.
Either way its order
is at least
$\lfloor\alpha\rfloor\ge h\ge k$,
a contradiction.
Thus edge deletion
destroys (F.1), and

$$\rho_G(V-X)=\lfloor\alpha|G-X|\rfloor+1.
 \tag{F.3}$$

Each root $x\in X$ has
an outside neighbor:
otherwise
$(X,V(G)-\{x\})$
has order $k-1$
and its far shore
$V(G)-X$ violates
(F.2). Summing degrees
over outside vertices
and outside-root
incidences gives

$$2\rho_G(V-X)
 =\sum_{x\in X}|N(x)-X|
  +\sum_{v\notin X}\deg_G(v).$$

If every outside vertex
had degree at least
$2\alpha$, the right
side would be at least
$k+2\alpha|G-X|>
2+2\alpha|G-X|$,
contradicting (F.3)
because $k\ge3$.
Thus some outside
vertex has degree
below $2\alpha$.
An isolated outside
vertex is impossible:
deleting it preserves
mass and the missing
rooted model, contrary
to minimality. This
completes (F.b).

For (F.c), suppose $J\subseteq G$
is $H$-universal. If
$k$ disjoint $X$–$J$
paths exist, trim them
at their first hits
of $J$, extend the
distinct arrival
vertices to an $h$-set
in $J$, and apply
universality there.
The induced branches
assigned to $X$,
extended along the
paths, give the
forbidden model.
Otherwise take a
minimum $X$–$J$
separation of order
below $k$. Minimum-cut
saturation gives
disjoint paths from
its adhesion into $J$.
The same attachment
argument makes its
far side universal
at the adhesion,
giving an $H$-rigid
separation forbidden
by (F.a). This
proves (F.c).

### F.2 Numerical closure

We record a sampling fact.
For a graph $Q$ on $n\ge2$
vertices and $0<p\le1$,
choose a uniform set of
$m=\min(n,\lceil pn\rceil+1)$
vertices. An edge has
both ends in that set
with probability
$m(m-1)/(n(n-1))\ge p^2$.
Thus some induced $L$
has

$$|L|\le pn+2,\qquad
 e(L)\ge p^2e(Q). \tag{F.4}$$

Choose the outside vertex
$v$ given by (F.b) with
minimum degree and put
$D=G[N[v]]$. It is not
isolated. It has an
outside-root neighbor:
if all its neighbors
were in $X$, contracting
one incident root edge
would give at least
$\lfloor\alpha\rfloor-(h-1)>0$
common neighbors outside
$X$, impossible.
The common-neighbor
bounds now give

$$|D|\le2\alpha+1,\qquad
 \delta(D)\ge\alpha-h. \tag{F.5}$$

Indeed $v$ and its outside-root
neighbors have at least
$\lfloor\alpha\rfloor+1$
neighbors in $D$, and a
root neighbor has at least
$1+\lfloor\alpha\rfloor-(h-1)$.
Put $Q_0=\lceil5c+2200h\rceil$.

Suppose first that
$\kappa(D)\ge Q_0$.
Fix any $h$-set
$Y\subseteq D$ and let
$n_1=|D-Y|$. Apply (F.4)
with $p=1/5$ to
$D-Y$, obtaining $L$ with

$$|L|\le n_1/5+2
 \le4.8c+2000h+3,$$
$$e(L)\ge e(D-Y)/25
 \ge(\delta(D)-h)n_1/50.$$

By (F.5),
$\delta(D)-h\ge12c+4998h$
and $n_1\ge\delta(D)-h+1\ge12c$.
Therefore
$e(L)-c|L|
 \ge[(2c+4998h)n_1/50]-2c>0$.
The density assumption
on $c$ gives an $H$
model $(S_i)$ in $L$.
Also

$$\kappa(D-L)
 \ge Q_0-|L|
 \ge0.2c+200h-3
 \ge16h.$$

For each $S_i$, choose
a distinct proxy $p_i$
outside $L\cup Y$
adjacent to one vertex
of $S_i$. This is
possible greedily:
$\delta(D)-|L|-h
 \ge7.2c+2998h-3>h$.
Appendix D links the
$h$ prescribed roots
of $Y$ to their assigned
proxies by disjoint
paths in $D-L$.
Adjoin these paths and
the proxy-to-branch
edges to $(S_i)$.
Because $Y$ and the
assignment were arbitrary,
$D$ is $H$-universal,
contradicting (F.c).

Thus $\kappa(D)<Q_0$.
Take a separation of
order below $Q_0$.
Since $\delta(D)>Q_0$,
we may enlarge its
adhesion to exactly
$Q_0$ by moving
vertices from a strict
side into the adhesion,
leaving both strict
sides nonempty. Orient
it as $(A,B)$ with
$|A|\le|B|$, put
$Z=A\cap B$ and
$N=A-Z$. Every vertex
of $N$ has all its
neighbors within
$N\cup Z$, so

$$|N|\ge\delta(D)-Q_0+1
 \ge7c+2799h>h. \tag{F.6}$$

Fix any $h$-set
$Y\subseteq N$ and
put $D_0=D[N-Y]$,
$n_0=|D_0|$.
By the smaller-side
choice and (F.5),

$$n_0\le(|D|-Q_0)/2-h
 \le10c+4000h,$$
$$\delta(D_0)\ge\delta(D)-Q_0-h
 \ge7c+2798h-1. \tag{F.7}$$

Apply (F.4) with
$p=1/3$ to $D_0$.
It gives an induced
$L'\subseteq D_0$
with $|L'|\le n_0/3+2$
and

$$e(L')\ge e(D_0)/9
 \ge\delta(D_0)n_0/18.$$

By (F.7),
$\delta(D_0)-6c
 \ge c+2798h-1$ and
$n_0\ge\delta(D_0)+1$.
Thus
$e(L')-c|L'|
 \ge[(\delta(D_0)-6c)n_0/18]-2c>0$.
Obtain an $H$ model
$(S_i)$ in $L'$.

Every vertex of $N$
has degree at least
$\delta(D)-Q_0
 \ge7c+2799h-1$
inside $D[N]$.
For any two nonadjacent
vertices of $N$, the
number of their common
neighbors outside
$L'$ is at least

$$\begin{aligned}
2\delta(D[N])-|N|-|L'|
 &\ge14c+5598h-2
       -\tfrac43n_0-h-2\\
 &\ge\tfrac23c+
       (263+\tfrac23)h-4
 \ge2h. \tag{F.8}
\end{aligned}$$

Choose one representative
$w_i\in S_i$ for each
branch. For any prescribed
bijection from $Y$ to
$V(H)$, join each
$y\in Y$ to its assigned
$w_i$ either by its
edge or by a two-edge
path through a fresh
common neighbor outside
$L'\cup Y$. Equation
(F.8) supplies at least
$2h$ candidates for
each nonedge; at most
$h-1$ other roots and
$h-1$ earlier internal
vertices are forbidden.
The paths are disjoint
and meet the model only
at their assigned
representatives. Adjoin
them to its branches.
Since $Y$ and its
assignment were
arbitrary, $D[N]$ is
$H$-universal,
contradicting (F.c).

Both cases contradict
the minimal counterexample.
Therefore every
$\alpha$-massed pair
with at most $h$
roots is $H$-universal
at its roots.

Finally let $G$ be
$h$-connected with
density at least
$\alpha$. For any
$h$-set $X$, (F.2)
is vacuous: an order-
below-$h$ separation
cannot have a nonempty
far side. Moreover

$$\rho_G(V-X)
 =e(G)-e(G[X])
 \ge\alpha|G|-\binom h2
 >\alpha(|G|-h),$$

because
$\alpha h>\binom h2$.
Thus $(G,X)$ is
$\alpha$-massed,
and the preceding
theorem gives the
required rooted model.
This completes the proof
of the rooted density
theorem.
