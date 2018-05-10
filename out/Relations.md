---
title     : "Relations: Inductive definition of relations"
layout    : page
permalink : /Relations
---

After having defined operations such as addition and multiplication,
the next step is to define relations, such as *less than or equal*.


## Imports

<pre class="Agda">{% raw %}<a id="273" class="Keyword">import</a> <a id="280" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="318" class="Symbol">as</a> <a id="321" class="Module">Eq</a>
<a id="324" class="Keyword">open</a> <a id="329" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="332" class="Keyword">using</a> <a id="338" class="Symbol">(</a><a id="339" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">_≡_</a><a id="342" class="Symbol">;</a> <a id="344" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="348" class="Symbol">;</a> <a id="350" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#981" class="Function">cong</a><a id="354" class="Symbol">;</a> <a id="356" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function">sym</a><a id="359" class="Symbol">)</a>
<a id="361" class="Keyword">open</a> <a id="366" class="Keyword">import</a> <a id="373" href="https://agda.github.io/agda-stdlib/Data.Nat.html" class="Module">Data.Nat</a> <a id="382" class="Keyword">using</a> <a id="388" class="Symbol">(</a><a id="389" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="390" class="Symbol">;</a> <a id="392" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="396" class="Symbol">;</a> <a id="398" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a><a id="401" class="Symbol">;</a> <a id="403" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">_+_</a><a id="406" class="Symbol">;</a> <a id="408" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#433" class="Primitive Operator">_*_</a><a id="411" class="Symbol">;</a> <a id="413" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#320" class="Primitive Operator">_∸_</a><a id="416" class="Symbol">)</a>
<a id="418" class="Keyword">open</a> <a id="423" class="Keyword">import</a> <a id="430" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="450" class="Keyword">using</a> <a id="456" class="Symbol">(</a><a id="457" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#8101" class="Function">+-comm</a><a id="463" class="Symbol">;</a> <a id="465" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#7665" class="Function">+-suc</a><a id="470" class="Symbol">)</a>{% endraw %}</pre>


## Defining relations

The relation *less than or equal* has an infinite number of
instances.  Here are a few of them:

    0 ≤ 0     0 ≤ 1     0 ≤ 2     0 ≤ 3     ...
              1 ≤ 1     1 ≤ 2     1 ≤ 3     ...
                        2 ≤ 2     2 ≤ 3     ...
                                  3 ≤ 3     ...
                                            ...

And yet, we can write a finite definition that encompasses
all of these instances in just a few lines.  Here is the
definition as a pair of inference rules:

    z≤n --------
        zero ≤ n

        m ≤ n
    s≤s -------------
        suc m ≤ suc n

And here is the definition in Agda:
<pre class="Agda">{% raw %}<a id="1147" class="Keyword">data</a> <a id="_≤_"></a><a id="1152" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">_≤_</a> <a id="1156" class="Symbol">:</a> <a id="1158" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="1160" class="Symbol">→</a> <a id="1162" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="1164" class="Symbol">→</a> <a id="1166" class="PrimitiveType">Set</a> <a id="1170" class="Keyword">where</a>
  <a id="_≤_.z≤n"></a><a id="1178" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1178" class="InductiveConstructor">z≤n</a> <a id="1182" class="Symbol">:</a> <a id="1184" class="Symbol">∀</a> <a id="1186" class="Symbol">{</a><a id="1187" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1187" class="Bound">m</a> <a id="1189" class="Symbol">:</a> <a id="1191" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="1192" class="Symbol">}</a> <a id="1194" class="Symbol">→</a> <a id="1196" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="1201" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="1203" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1187" class="Bound">m</a>
  <a id="_≤_.s≤s"></a><a id="1207" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1207" class="InductiveConstructor">s≤s</a> <a id="1211" class="Symbol">:</a> <a id="1213" class="Symbol">∀</a> <a id="1215" class="Symbol">{</a><a id="1216" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1216" class="Bound">m</a> <a id="1218" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1218" class="Bound">n</a> <a id="1220" class="Symbol">:</a> <a id="1222" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="1223" class="Symbol">}</a> <a id="1225" class="Symbol">→</a> <a id="1227" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1216" class="Bound">m</a> <a id="1229" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="1231" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1218" class="Bound">n</a> <a id="1233" class="Symbol">→</a> <a id="1235" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="1239" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1216" class="Bound">m</a> <a id="1241" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="1243" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="1247" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1218" class="Bound">n</a>{% endraw %}</pre>
Here `z≤n` and `s≤s` (with no spaces) are constructor names,
while `zero ≤ m`, and `m ≤ n` and `suc m ≤ suc n` (with spaces)
are types.  This is our first use of an *indexed* datatype,
where we say the type `m ≤ n` is indexed by two naturals, `m` and `n`.

Both definitions above tell us the same two things:

+ *Base case*: for all naturals `n`, the proposition `zero ≤ n` holds
+ *Inductive case*: for all naturals `m` and `n`, if the proposition
  `m ≤ n` holds, then the proposition `suc m ≤ suc n` holds.

In fact, they each give us a bit more detail:

+ *Base case*: for all naturals `n`, the constructor `z≤n` 
  produces evidence that `zero ≤ n` holds.
+ *Inductive case*: for all naturals `m` and `n`, the constructor
  `s≤s` takes evidence that `m ≤ n` holds into evidence that
  `suc m ≤ suc n` holds.

For example, here in inference rule notation is the proof that
`2 ≤ 4`.

      z≤n -----
          0 ≤ 2
     s≤s -------
          1 ≤ 3
    s≤s ---------
          2 ≤ 4

And here is the corresponding Agda proof.
<pre class="Agda">{% raw %}<a id="2302" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#2302" class="Function">_</a> <a id="2304" class="Symbol">:</a> <a id="2306" class="Number">2</a> <a id="2308" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="2310" class="Number">4</a>
<a id="2312" class="Symbol">_</a> <a id="2314" class="Symbol">=</a> <a id="2316" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1207" class="InductiveConstructor">s≤s</a> <a id="2320" class="Symbol">(</a><a id="2321" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1207" class="InductiveConstructor">s≤s</a> <a id="2325" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1178" class="InductiveConstructor">z≤n</a><a id="2328" class="Symbol">)</a>{% endraw %}</pre>


## Implicit arguments

This is our first use of implicit arguments.
In the definition of inequality, the two lines defining the constructors
use `∀`, very similar to our use of `∀` in propositions such as:

    +-comm : ∀ (m n : ℕ) → m + n ≡ n + m

However, here the declarations are surrounded by curly braces `{ }` rather than
parentheses `( )`.  This means that the arguments are *implicit* and need not be
written explicitly; instead, they are *inferred* by Agda's typechecker. Thus, we
write `+-comm m n` for the proof that `m + n ≡ n + m`, but `z≤n` for the proof
that `zero ≤ m`, leaving `m` implicit.  Similarly, if `m≤n` is evidence that
`m ≤ n`, we write write `s≤s m≤n` for evidence that `suc m ≤ suc n`, leaving
both `m` and `n` implicit.

If we wish, it is possible to provide implicit arguments explicitly by
writing the arguments inside curly braces.  For instance, here is the
Agda proof that `2 ≤ 4` repeated, with the implicit arguments made
explicit.
<pre class="Agda">{% raw %}<a id="3326" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#3326" class="Function">_</a> <a id="3328" class="Symbol">:</a> <a id="3330" class="Number">2</a> <a id="3332" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="3334" class="Number">4</a>
<a id="3336" class="Symbol">_</a> <a id="3338" class="Symbol">=</a> <a id="3340" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1207" class="InductiveConstructor">s≤s</a> <a id="3344" class="Symbol">{</a><a id="3345" class="Number">1</a><a id="3346" class="Symbol">}</a> <a id="3348" class="Symbol">{</a><a id="3349" class="Number">3</a><a id="3350" class="Symbol">}</a> <a id="3352" class="Symbol">(</a><a id="3353" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1207" class="InductiveConstructor">s≤s</a> <a id="3357" class="Symbol">{</a><a id="3358" class="Number">0</a><a id="3359" class="Symbol">}</a> <a id="3361" class="Symbol">{</a><a id="3362" class="Number">2</a><a id="3363" class="Symbol">}</a> <a id="3365" class="Symbol">(</a><a id="3366" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1178" class="InductiveConstructor">z≤n</a> <a id="3370" class="Symbol">{</a><a id="3371" class="Number">2</a><a id="3372" class="Symbol">}))</a>{% endraw %}</pre>


## Precedence

We declare the precedence for comparison as follows.
<pre class="Agda">{% raw %}<a id="3470" class="Keyword">infix</a> <a id="3476" class="Number">4</a> <a id="3478" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">_≤_</a>{% endraw %}</pre>
We set the precedence of `_≤_` at level 4, so it binds less tightly
that `_+_` at level 6 and hence `1 + 2 ≤ 3` parses as `(1 + 2) ≤ 3`.
We write `infix` to indicate that the operator does not associate to
either the left or right, as it makes no sense to parse `1 ≤ 2 ≤ 3` as
either `(1 ≤ 2) ≤ 3` or `1 ≤ (2 ≤ 3)`.


## Decidability

Given two numbers, it is straightforward to compute whether or not the first is
less than or equal to the second.  We don't give the code for doing so here, but
will return to this point in Chapter [Decidability](Decidability).


## Properties of ordering relations

Relations occur all the time, and mathematicians have agreed
on names for some of the most common properties.

+ *Reflexive* For all `n`, the relation `n ≤ n` holds.
+ *Transitive* For all `m`, `n`, and `p`, if `m ≤ n` and
`n ≤ p` hold, then `m ≤ p` holds.
+ *Anti-symmetric* For all `m` and `n`, if both `m ≤ n` and
`n ≤ m` hold, then `m ≡ n` holds.
+ *Total* For all `m` and `n`, either `m ≤ n` or `n ≤ m`
holds.

The relation `_≤_` satisfies all four of these properties.

There are also names for some combinations of these properties.

+ *Preorder* Any relation that is reflexive and transitive.
+ *Partial order* Any preorder that is also anti-symmetric.
+ *Total order* Any partial order that is also total.

If you ever bump into a relation at a party, you now know how
to make small talk, by asking it whether it is reflexive, transitive,
anti-symmetric, and total. Or instead you might ask whether it is a
preorder, partial order, or total order.

Less frivolously, if you ever bump into a relation while reading
a technical paper, this gives you an easy way to orient yourself,
by checking whether or not it is a preorder, partial order, or total order.
A careful author will often make it explicit, for instance by saying
that a given relation is a preorder but not a partial order, or a
partial order but not a total order. (Can you think of examples of
such relations?)


## Reflexivity

The first property to prove about comparison is that it is reflexive:
for any natural `n`, the relation `n ≤ n` holds.
<pre class="Agda">{% raw %}<a id="≤-refl"></a><a id="5629" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#5629" class="Function">≤-refl</a> <a id="5636" class="Symbol">:</a> <a id="5638" class="Symbol">∀</a> <a id="5640" class="Symbol">{</a><a id="5641" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#5641" class="Bound">n</a> <a id="5643" class="Symbol">:</a> <a id="5645" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="5646" class="Symbol">}</a> <a id="5648" class="Symbol">→</a> <a id="5650" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#5641" class="Bound">n</a> <a id="5652" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="5654" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#5641" class="Bound">n</a>
<a id="5656" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#5629" class="Function">≤-refl</a> <a id="5663" class="Symbol">{</a><a id="5664" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="5668" class="Symbol">}</a> <a id="5670" class="Symbol">=</a> <a id="5672" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1178" class="InductiveConstructor">z≤n</a>
<a id="5676" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#5629" class="Function">≤-refl</a> <a id="5683" class="Symbol">{</a><a id="5684" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="5688" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#5688" class="Bound">n</a><a id="5689" class="Symbol">}</a> <a id="5691" class="Symbol">=</a> <a id="5693" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1207" class="InductiveConstructor">s≤s</a> <a id="5697" class="Symbol">(</a><a id="5698" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#5629" class="Function">≤-refl</a> <a id="5705" class="Symbol">{</a><a id="5706" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#5688" class="Bound">n</a><a id="5707" class="Symbol">})</a>{% endraw %}</pre>
The proof is a straightforward induction on `n`.  In the base case,
`zero ≤ zero` holds by `z≤n`.  In the inductive case, the inductive
hypothesis `≤-refl n` gives us a proof of `n ≤ n`, and applying `s≤s`
to that yields a proof of `suc n ≤ suc n`.

It is a good exercise to prove reflexivity interactively in Emacs,
using holes and the `^C ^C`, `^C ^,`, and `^C ^R` commands.


## Transitivity

The second property to prove about comparison is that it is
transitive: for any naturals `m`, `n`, and `p`, if `m ≤ n` and `n ≤
p` hold, then `m ≤ p` holds.
<pre class="Agda">{% raw %}<a id="≤-trans"></a><a id="6287" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#6287" class="Function">≤-trans</a> <a id="6295" class="Symbol">:</a> <a id="6297" class="Symbol">∀</a> <a id="6299" class="Symbol">{</a><a id="6300" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#6300" class="Bound">m</a> <a id="6302" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#6302" class="Bound">n</a> <a id="6304" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#6304" class="Bound">p</a> <a id="6306" class="Symbol">:</a> <a id="6308" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="6309" class="Symbol">}</a> <a id="6311" class="Symbol">→</a> <a id="6313" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#6300" class="Bound">m</a> <a id="6315" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="6317" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#6302" class="Bound">n</a> <a id="6319" class="Symbol">→</a> <a id="6321" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#6302" class="Bound">n</a> <a id="6323" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="6325" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#6304" class="Bound">p</a> <a id="6327" class="Symbol">→</a> <a id="6329" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#6300" class="Bound">m</a> <a id="6331" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="6333" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#6304" class="Bound">p</a>
<a id="6335" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#6287" class="Function">≤-trans</a> <a id="6343" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1178" class="InductiveConstructor">z≤n</a> <a id="6347" class="Symbol">_</a> <a id="6349" class="Symbol">=</a> <a id="6351" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1178" class="InductiveConstructor">z≤n</a>
<a id="6355" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#6287" class="Function">≤-trans</a> <a id="6363" class="Symbol">(</a><a id="6364" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1207" class="InductiveConstructor">s≤s</a> <a id="6368" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#6368" class="Bound">m≤n</a><a id="6371" class="Symbol">)</a> <a id="6373" class="Symbol">(</a><a id="6374" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1207" class="InductiveConstructor">s≤s</a> <a id="6378" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#6378" class="Bound">n≤p</a><a id="6381" class="Symbol">)</a> <a id="6383" class="Symbol">=</a> <a id="6385" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1207" class="InductiveConstructor">s≤s</a> <a id="6389" class="Symbol">(</a><a id="6390" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#6287" class="Function">≤-trans</a> <a id="6398" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#6368" class="Bound">m≤n</a> <a id="6402" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#6378" class="Bound">n≤p</a><a id="6405" class="Symbol">)</a>{% endraw %}</pre>
Here the proof is most easily thought of as by induction on the
*evidence* that `m ≤ n`, so we have left `m`, `n`, and `p` implicit.

In the base case, the first inequality holds by `z≤n`, and so
we are given `zero ≤ n` and `n ≤ p` and must show `zero ≤ p`,
which follows immediately by `z≤n`.  In this
case, the fact that `n ≤ p` is irrelevant, and we write `_` as the
pattern to indicate that the corresponding evidence is unused.

In the inductive case, the first inequality holds by `s≤s m≤n`
and the second inequality by `s≤s n≤p`, and so we are given
`suc m ≤ suc n` and `suc n ≤ suc p`, and must show `suc m ≤ suc p`.
The inductive hypothesis `≤-trans m≤n n≤p` establishes
that `m ≤ p`, and our goal follows by applying `s≤s`.

<!--

In the base case, `m ≤ n` holds by `z≤n`, so it must be that
`m` is `zero`, in which case `m ≤ p` also holds by `z≤n`. In this
case, the fact that `n ≤ p` is irrelevant, and we write `_` as the
pattern to indicate that the corresponding evidence is unused.

In the inductive case, `m ≤ n` holds by `s≤s m≤n`, so it must be that `m`
is `suc m′` and `n` is `suc n′` for some `m′` and `n′`, and `m≤n` is
evidence that `m′ ≤ n′`.  In this case, the only way that `p ≤ n` can
hold is by `s≤s n≤p`, where `p` is `suc p′` for some `p′` and `n≤p` is
evidence that `n′ ≤ p′`.  The inductive hypothesis `≤-trans m≤n n≤p`
provides evidence that `m′ ≤ p′`, and applying `s≤s` to that gives
evidence of the desired conclusion, `suc m′ ≤ suc p′`.

-->

The case `≤-trans (s≤s m≤n) z≤n` cannot arise, since the first
inequality implies the middle value is `suc n` while the second
inequality implies that it is `zero`.  Agda can determine that
such a case cannot arise, and does not require it to be listed.

Alternatively, we could make the implicit parameters explicit.
<pre class="Agda">{% raw %}<a id="≤-trans′"></a><a id="8229" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8229" class="Function">≤-trans′</a> <a id="8238" class="Symbol">:</a> <a id="8240" class="Symbol">∀</a> <a id="8242" class="Symbol">(</a><a id="8243" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8243" class="Bound">m</a> <a id="8245" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8245" class="Bound">n</a> <a id="8247" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8247" class="Bound">p</a> <a id="8249" class="Symbol">:</a> <a id="8251" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="8252" class="Symbol">)</a> <a id="8254" class="Symbol">→</a> <a id="8256" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8243" class="Bound">m</a> <a id="8258" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="8260" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8245" class="Bound">n</a> <a id="8262" class="Symbol">→</a> <a id="8264" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8245" class="Bound">n</a> <a id="8266" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="8268" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8247" class="Bound">p</a> <a id="8270" class="Symbol">→</a> <a id="8272" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8243" class="Bound">m</a> <a id="8274" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="8276" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8247" class="Bound">p</a>
<a id="8278" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8229" class="Function">≤-trans′</a> <a id="8287" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="8292" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8292" class="Bound">n</a> <a id="8294" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8294" class="Bound">p</a> <a id="8296" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1178" class="InductiveConstructor">z≤n</a> <a id="8300" class="Symbol">_</a> <a id="8302" class="Symbol">=</a> <a id="8304" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1178" class="InductiveConstructor">z≤n</a>
<a id="8308" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8229" class="Function">≤-trans′</a> <a id="8317" class="Symbol">(</a><a id="8318" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="8322" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8322" class="Bound">m</a><a id="8323" class="Symbol">)</a> <a id="8325" class="Symbol">(</a><a id="8326" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="8330" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8330" class="Bound">n</a><a id="8331" class="Symbol">)</a> <a id="8333" class="Symbol">(</a><a id="8334" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="8338" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8338" class="Bound">p</a><a id="8339" class="Symbol">)</a> <a id="8341" class="Symbol">(</a><a id="8342" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1207" class="InductiveConstructor">s≤s</a> <a id="8346" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8346" class="Bound">m≤n</a><a id="8349" class="Symbol">)</a> <a id="8351" class="Symbol">(</a><a id="8352" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1207" class="InductiveConstructor">s≤s</a> <a id="8356" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8356" class="Bound">n≤p</a><a id="8359" class="Symbol">)</a> <a id="8361" class="Symbol">=</a> <a id="8363" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1207" class="InductiveConstructor">s≤s</a> <a id="8367" class="Symbol">(</a><a id="8368" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8229" class="Function">≤-trans′</a> <a id="8377" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8322" class="Bound">m</a> <a id="8379" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8330" class="Bound">n</a> <a id="8381" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8338" class="Bound">p</a> <a id="8383" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8346" class="Bound">m≤n</a> <a id="8387" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#8356" class="Bound">n≤p</a><a id="8390" class="Symbol">)</a>{% endraw %}</pre>
One might argue that this is clearer or one might argue that the extra
length obscures the essence of the proof.  We will usually opt for
shorter proofs.

The technique of inducting on evidence that a property holds (e.g.,
inducting on evidence that `m ≤ n`)---rather than induction on the
value of which the property holds (e.g., inducting on `m`)---will turn
out to be immensely valuable, and one that we use often.

Again, it is a good exercise to prove transitivity interactively in Emacs,
using holes and the `^C ^C`, `^C ^,`, and `^C ^R` commands.


## Anti-symmetry

The third property to prove about comparison is that it is antisymmetric:
for all naturals `m` and `n`, if both `m ≤ n` and `n ≤ m` hold, then
`m ≡ n` holds.
<pre class="Agda">{% raw %}<a id="≤-antisym"></a><a id="9148" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#9148" class="Function">≤-antisym</a> <a id="9158" class="Symbol">:</a> <a id="9160" class="Symbol">∀</a> <a id="9162" class="Symbol">{</a><a id="9163" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#9163" class="Bound">m</a> <a id="9165" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#9165" class="Bound">n</a> <a id="9167" class="Symbol">:</a> <a id="9169" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="9170" class="Symbol">}</a> <a id="9172" class="Symbol">→</a> <a id="9174" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#9163" class="Bound">m</a> <a id="9176" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="9178" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#9165" class="Bound">n</a> <a id="9180" class="Symbol">→</a> <a id="9182" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#9165" class="Bound">n</a> <a id="9184" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="9186" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#9163" class="Bound">m</a> <a id="9188" class="Symbol">→</a> <a id="9190" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#9163" class="Bound">m</a> <a id="9192" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="9194" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#9165" class="Bound">n</a>
<a id="9196" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#9148" class="Function">≤-antisym</a> <a id="9206" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1178" class="InductiveConstructor">z≤n</a> <a id="9210" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1178" class="InductiveConstructor">z≤n</a> <a id="9214" class="Symbol">=</a> <a id="9216" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>
<a id="9221" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#9148" class="Function">≤-antisym</a> <a id="9231" class="Symbol">(</a><a id="9232" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1207" class="InductiveConstructor">s≤s</a> <a id="9236" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#9236" class="Bound">m≤n</a><a id="9239" class="Symbol">)</a> <a id="9241" class="Symbol">(</a><a id="9242" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1207" class="InductiveConstructor">s≤s</a> <a id="9246" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#9246" class="Bound">n≤m</a><a id="9249" class="Symbol">)</a> <a id="9251" class="Symbol">=</a> <a id="9253" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#981" class="Function">cong</a> <a id="9258" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="9262" class="Symbol">(</a><a id="9263" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#9148" class="Function">≤-antisym</a> <a id="9273" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#9236" class="Bound">m≤n</a> <a id="9277" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#9246" class="Bound">n≤m</a><a id="9280" class="Symbol">)</a>{% endraw %}</pre>
Again, the proof is by induction over the evidence that `m ≤ n`
and `n ≤ m` hold, and so we have left `m` and `n` implicit.

In the base case, both inequalities hold by `z≤n`,
and so we are given `zero ≤ zero` and `zero ≤ zero` and must
show `zero ≡ zero`, which follows by reflexivity.  (Reflexivity
of equality, that is, not reflexivity of inequality.)

In the inductive case, the first inequality holds by `s≤s m≤n`
and the second inequality holds by `s≤s n≤m`, and so we are
given `suc m ≤ suc n` and `suc n ≤ suc m` and must show `suc m ≡ suc n`.
The inductive hypothesis `≤-antisym m≤n n≤m` establishes that `m ≡ n`,
and our goal follows by congruence.


## Total

The fourth property to prove about comparison is that it is total:
for any naturals `m` and `n` either `m ≤ n` or `n ≤ m`, or both if
`m` and `n` are equal.

We specify what it means for inequality to be total.
<pre class="Agda">{% raw %}<a id="10188" class="Keyword">data</a> <a id="Total"></a><a id="10193" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10193" class="Datatype">Total</a> <a id="10199" class="Symbol">(</a><a id="10200" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10200" class="Bound">m</a> <a id="10202" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10202" class="Bound">n</a> <a id="10204" class="Symbol">:</a> <a id="10206" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="10207" class="Symbol">)</a> <a id="10209" class="Symbol">:</a> <a id="10211" class="PrimitiveType">Set</a> <a id="10215" class="Keyword">where</a>
  <a id="Total.forward"></a><a id="10223" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10223" class="InductiveConstructor">forward</a> <a id="10231" class="Symbol">:</a> <a id="10233" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10200" class="Bound">m</a> <a id="10235" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="10237" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10202" class="Bound">n</a> <a id="10239" class="Symbol">→</a> <a id="10241" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10193" class="Datatype">Total</a> <a id="10247" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10200" class="Bound">m</a> <a id="10249" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10202" class="Bound">n</a>
  <a id="Total.flipped"></a><a id="10253" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10253" class="InductiveConstructor">flipped</a> <a id="10261" class="Symbol">:</a> <a id="10263" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10202" class="Bound">n</a> <a id="10265" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="10267" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10200" class="Bound">m</a> <a id="10269" class="Symbol">→</a> <a id="10271" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10193" class="Datatype">Total</a> <a id="10277" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10200" class="Bound">m</a> <a id="10279" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10202" class="Bound">n</a>{% endraw %}</pre>
Evidence that `Total m n` holds is either of the form
`forward m≤n` or `flipped n≤m`, where `m≤n` and `n≤m` are
evidence of `m ≤ n` and `n ≤ m` respectively.

This is our first use of a datatype with *parameters*,
in this case `m` and `n`.  It is equivalent to the following
indexed datatype.
<pre class="Agda">{% raw %}<a id="10598" class="Keyword">data</a> <a id="Total′"></a><a id="10603" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10603" class="Datatype">Total′</a> <a id="10610" class="Symbol">:</a> <a id="10612" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="10614" class="Symbol">→</a> <a id="10616" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="10618" class="Symbol">→</a> <a id="10620" class="PrimitiveType">Set</a> <a id="10624" class="Keyword">where</a>
  <a id="Total′.forward′"></a><a id="10632" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10632" class="InductiveConstructor">forward′</a> <a id="10641" class="Symbol">:</a> <a id="10643" class="Symbol">∀</a> <a id="10645" class="Symbol">{</a><a id="10646" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10646" class="Bound">m</a> <a id="10648" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10648" class="Bound">n</a> <a id="10650" class="Symbol">:</a> <a id="10652" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="10653" class="Symbol">}</a> <a id="10655" class="Symbol">→</a> <a id="10657" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10646" class="Bound">m</a> <a id="10659" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="10661" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10648" class="Bound">n</a> <a id="10663" class="Symbol">→</a> <a id="10665" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10603" class="Datatype">Total′</a> <a id="10672" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10646" class="Bound">m</a> <a id="10674" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10648" class="Bound">n</a>
  <a id="Total′.flipped′"></a><a id="10678" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10678" class="InductiveConstructor">flipped′</a> <a id="10687" class="Symbol">:</a> <a id="10689" class="Symbol">∀</a> <a id="10691" class="Symbol">{</a><a id="10692" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10692" class="Bound">m</a> <a id="10694" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10694" class="Bound">n</a> <a id="10696" class="Symbol">:</a> <a id="10698" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="10699" class="Symbol">}</a> <a id="10701" class="Symbol">→</a> <a id="10703" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10694" class="Bound">n</a> <a id="10705" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="10707" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10692" class="Bound">m</a> <a id="10709" class="Symbol">→</a> <a id="10711" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10603" class="Datatype">Total′</a> <a id="10718" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10692" class="Bound">m</a> <a id="10720" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10694" class="Bound">n</a>{% endraw %}</pre>
Each parameter of the type translates as an implicit
parameter of each constructor.
Unlike an indexed datatype, where the indexes can vary
(as in `zero ≤ n` and `suc m ≤ suc n`), in a parameterised
datatype the parameters must always be the same (as in `Total m n`).
Parameterised declarations are shorter, easier to read, and let Agda
exploit the uniformity of the parameters, so we will use them in
preference to indexed types when possible.

With that preliminary out of the way, we specify and prove totality.
<pre class="Agda">{% raw %}<a id="≤-total"></a><a id="11260" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#11260" class="Function">≤-total</a> <a id="11268" class="Symbol">:</a> <a id="11270" class="Symbol">∀</a> <a id="11272" class="Symbol">(</a><a id="11273" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#11273" class="Bound">m</a> <a id="11275" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#11275" class="Bound">n</a> <a id="11277" class="Symbol">:</a> <a id="11279" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="11280" class="Symbol">)</a> <a id="11282" class="Symbol">→</a> <a id="11284" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10193" class="Datatype">Total</a> <a id="11290" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#11273" class="Bound">m</a> <a id="11292" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#11275" class="Bound">n</a>
<a id="11294" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#11260" class="Function">≤-total</a> <a id="11302" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="11310" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#11310" class="Bound">n</a>                         <a id="11336" class="Symbol">=</a>  <a id="11339" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10223" class="InductiveConstructor">forward</a> <a id="11347" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1178" class="InductiveConstructor">z≤n</a>
<a id="11351" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#11260" class="Function">≤-total</a> <a id="11359" class="Symbol">(</a><a id="11360" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11364" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#11364" class="Bound">m</a><a id="11365" class="Symbol">)</a> <a id="11367" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>                      <a id="11393" class="Symbol">=</a>  <a id="11396" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10253" class="InductiveConstructor">flipped</a> <a id="11404" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1178" class="InductiveConstructor">z≤n</a>
<a id="11408" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#11260" class="Function">≤-total</a> <a id="11416" class="Symbol">(</a><a id="11417" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11421" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#11421" class="Bound">m</a><a id="11422" class="Symbol">)</a> <a id="11424" class="Symbol">(</a><a id="11425" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11429" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#11429" class="Bound">n</a><a id="11430" class="Symbol">)</a> <a id="11432" class="Keyword">with</a> <a id="11437" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#11260" class="Function">≤-total</a> <a id="11445" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#11421" class="Bound">m</a> <a id="11447" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#11429" class="Bound">n</a>
<a id="11449" class="Symbol">...</a>                        <a id="11476" class="Symbol">|</a> <a id="11478" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10223" class="InductiveConstructor">forward</a> <a id="11486" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#11486" class="Bound">m≤n</a>  <a id="11491" class="Symbol">=</a>  <a id="11494" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10223" class="InductiveConstructor">forward</a> <a id="11502" class="Symbol">(</a><a id="11503" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1207" class="InductiveConstructor">s≤s</a> <a id="11507" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#11486" class="Bound">m≤n</a><a id="11510" class="Symbol">)</a>
<a id="11512" class="Symbol">...</a>                        <a id="11539" class="Symbol">|</a> <a id="11541" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10253" class="InductiveConstructor">flipped</a> <a id="11549" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#11549" class="Bound">n≤m</a>  <a id="11554" class="Symbol">=</a>  <a id="11557" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10253" class="InductiveConstructor">flipped</a> <a id="11565" class="Symbol">(</a><a id="11566" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1207" class="InductiveConstructor">s≤s</a> <a id="11570" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#11549" class="Bound">n≤m</a><a id="11573" class="Symbol">)</a>{% endraw %}</pre>
In this case the proof is by induction over both the first
and second arguments.  We perform a case analysis:

+ *First base case*: If the first argument is `zero` and the
  second argument is `n` then the forward case holds, 
  with `z≤n` as evidence that `zero ≤ n`.

+ *Second base case*: If the first argument is `suc m` and the
  second argument is `zero` then the flipped case holds, with
  `z≤n` as evidence that `zero ≤ suc m`.

+ *Inductive case*: If the first argument is `suc m` and the
  second argument is `suc n`, then the inductive hypothesis
  `≤-total m n` establishes one of the following:

  - The forward case of the inductive hypothesis holds with `m≤n` as
    evidence that `m ≤ n`, from which it follows that the forward case of the
    proposition holds with `s≤s m≤n` as evidence that `suc m ≤ suc n`.

  - The flipped case of the inductive hypothesis holds with `n≤m` as
    evidence that `n ≤ m`, from which it follows that the flipped case of the
    proposition holds with `s≤s n≤m` as evidence that `suc n ≤ suc m`.

This is our first use of the `with` clause in Agda.  The keyword
`with` is followed by an expression and one or more subsequent lines.
Each line begins with an ellipsis (`...`) and a vertical bar (`|`),
followed by a pattern to be matched against the expression
and the right-hand side of the equation.

Every use of `with` is equivalent to defining a helper function.  For
example, the definition above is equivalent to the following.
<pre class="Agda">{% raw %}<a id="≤-total′"></a><a id="13082" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13082" class="Function">≤-total′</a> <a id="13091" class="Symbol">:</a> <a id="13093" class="Symbol">∀</a> <a id="13095" class="Symbol">(</a><a id="13096" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13096" class="Bound">m</a> <a id="13098" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13098" class="Bound">n</a> <a id="13100" class="Symbol">:</a> <a id="13102" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="13103" class="Symbol">)</a> <a id="13105" class="Symbol">→</a> <a id="13107" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10193" class="Datatype">Total</a> <a id="13113" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13096" class="Bound">m</a> <a id="13115" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13098" class="Bound">n</a>
<a id="13117" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13082" class="Function">≤-total′</a> <a id="13126" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="13134" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13134" class="Bound">n</a>        <a id="13143" class="Symbol">=</a>  <a id="13146" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10223" class="InductiveConstructor">forward</a> <a id="13154" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1178" class="InductiveConstructor">z≤n</a>
<a id="13158" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13082" class="Function">≤-total′</a> <a id="13167" class="Symbol">(</a><a id="13168" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13172" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13172" class="Bound">m</a><a id="13173" class="Symbol">)</a> <a id="13175" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>     <a id="13184" class="Symbol">=</a>  <a id="13187" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10253" class="InductiveConstructor">flipped</a> <a id="13195" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1178" class="InductiveConstructor">z≤n</a>
<a id="13199" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13082" class="Function">≤-total′</a> <a id="13208" class="Symbol">(</a><a id="13209" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13213" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13213" class="Bound">m</a><a id="13214" class="Symbol">)</a> <a id="13216" class="Symbol">(</a><a id="13217" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13221" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13221" class="Bound">n</a><a id="13222" class="Symbol">)</a>  <a id="13225" class="Symbol">=</a>  <a id="13228" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13260" class="Function">helper</a> <a id="13235" class="Symbol">(</a><a id="13236" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13082" class="Function">≤-total′</a> <a id="13245" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13213" class="Bound">m</a> <a id="13247" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13221" class="Bound">n</a><a id="13248" class="Symbol">)</a>
  <a id="13252" class="Keyword">where</a>
  <a id="13260" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13260" class="Function">helper</a> <a id="13267" class="Symbol">:</a> <a id="13269" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10193" class="Datatype">Total</a> <a id="13275" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13213" class="Bound">m</a> <a id="13277" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13221" class="Bound">n</a> <a id="13279" class="Symbol">→</a> <a id="13281" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10193" class="Datatype">Total</a> <a id="13287" class="Symbol">(</a><a id="13288" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13292" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13213" class="Bound">m</a><a id="13293" class="Symbol">)</a> <a id="13295" class="Symbol">(</a><a id="13296" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13300" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13221" class="Bound">n</a><a id="13301" class="Symbol">)</a>
  <a id="13305" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13260" class="Function">helper</a> <a id="13312" class="Symbol">(</a><a id="13313" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10223" class="InductiveConstructor">forward</a> <a id="13321" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13321" class="Bound">m≤n</a><a id="13324" class="Symbol">)</a>  <a id="13327" class="Symbol">=</a>  <a id="13330" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10223" class="InductiveConstructor">forward</a> <a id="13338" class="Symbol">(</a><a id="13339" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1207" class="InductiveConstructor">s≤s</a> <a id="13343" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13321" class="Bound">m≤n</a><a id="13346" class="Symbol">)</a>
  <a id="13350" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13260" class="Function">helper</a> <a id="13357" class="Symbol">(</a><a id="13358" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10253" class="InductiveConstructor">flipped</a> <a id="13366" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13366" class="Bound">n≤m</a><a id="13369" class="Symbol">)</a>  <a id="13372" class="Symbol">=</a>  <a id="13375" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10253" class="InductiveConstructor">flipped</a> <a id="13383" class="Symbol">(</a><a id="13384" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1207" class="InductiveConstructor">s≤s</a> <a id="13388" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#13366" class="Bound">n≤m</a><a id="13391" class="Symbol">)</a>{% endraw %}</pre>
This is also our first use of a `where` clause in Agda.  The keyword `where` is
followed by one or more definitions, which must be indented.  Any variables
bound of the left-hand side of the preceding equation (in this case, `m` and
`n`) are in scope within the nested definition, and any identifiers bound in the
nested definition (in this case, `helper`) are in scope in the right-hand side
of the preceding equation.

If both arguments are equal, then both cases hold and we could return evidence
of either.  In the code above we return the forward case, but there is a
variant that returns the flipped case.
<pre class="Agda">{% raw %}<a id="≤-total″"></a><a id="14029" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14029" class="Function">≤-total″</a> <a id="14038" class="Symbol">:</a> <a id="14040" class="Symbol">∀</a> <a id="14042" class="Symbol">(</a><a id="14043" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14043" class="Bound">m</a> <a id="14045" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14045" class="Bound">n</a> <a id="14047" class="Symbol">:</a> <a id="14049" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="14050" class="Symbol">)</a> <a id="14052" class="Symbol">→</a> <a id="14054" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10193" class="Datatype">Total</a> <a id="14060" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14043" class="Bound">m</a> <a id="14062" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14045" class="Bound">n</a>
<a id="14064" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14029" class="Function">≤-total″</a> <a id="14073" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14073" class="Bound">m</a>       <a id="14081" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>                      <a id="14107" class="Symbol">=</a>  <a id="14110" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10253" class="InductiveConstructor">flipped</a> <a id="14118" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1178" class="InductiveConstructor">z≤n</a>
<a id="14122" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14029" class="Function">≤-total″</a> <a id="14131" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="14139" class="Symbol">(</a><a id="14140" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14144" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14144" class="Bound">n</a><a id="14145" class="Symbol">)</a>                   <a id="14165" class="Symbol">=</a>  <a id="14168" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10223" class="InductiveConstructor">forward</a> <a id="14176" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1178" class="InductiveConstructor">z≤n</a>
<a id="14180" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14029" class="Function">≤-total″</a> <a id="14189" class="Symbol">(</a><a id="14190" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14194" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14194" class="Bound">m</a><a id="14195" class="Symbol">)</a> <a id="14197" class="Symbol">(</a><a id="14198" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14202" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14202" class="Bound">n</a><a id="14203" class="Symbol">)</a> <a id="14205" class="Keyword">with</a> <a id="14210" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14029" class="Function">≤-total″</a> <a id="14219" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14194" class="Bound">m</a> <a id="14221" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14202" class="Bound">n</a>
<a id="14223" class="Symbol">...</a>                        <a id="14250" class="Symbol">|</a> <a id="14252" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10223" class="InductiveConstructor">forward</a> <a id="14260" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14260" class="Bound">m≤n</a>   <a id="14266" class="Symbol">=</a>  <a id="14269" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10223" class="InductiveConstructor">forward</a> <a id="14277" class="Symbol">(</a><a id="14278" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1207" class="InductiveConstructor">s≤s</a> <a id="14282" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14260" class="Bound">m≤n</a><a id="14285" class="Symbol">)</a>
<a id="14287" class="Symbol">...</a>                        <a id="14314" class="Symbol">|</a> <a id="14316" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10253" class="InductiveConstructor">flipped</a> <a id="14324" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14324" class="Bound">n≤m</a>   <a id="14330" class="Symbol">=</a>  <a id="14333" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#10253" class="InductiveConstructor">flipped</a> <a id="14341" class="Symbol">(</a><a id="14342" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1207" class="InductiveConstructor">s≤s</a> <a id="14346" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14324" class="Bound">n≤m</a><a id="14349" class="Symbol">)</a>{% endraw %}</pre>
It differs from the original code in that it pattern
matches on the second argument before the first argument.


## Monotonicity

If one bumps into both an operator and an ordering at a party, one may ask if
the operator is *monotonic* with regard to the ordering.  For example, addition
is monotonic with regard to inequality, meaning

  ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q

The proof is straightforward using the techniques we have learned, and is best
broken into three parts. First, we deal with the special case of showing
addition is monotonic on the right.
<pre class="Agda">{% raw %}<a id="+-monoʳ-≤"></a><a id="14951" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14951" class="Function">+-monoʳ-≤</a> <a id="14961" class="Symbol">:</a> <a id="14963" class="Symbol">∀</a> <a id="14965" class="Symbol">(</a><a id="14966" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14966" class="Bound">m</a> <a id="14968" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14968" class="Bound">p</a> <a id="14970" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14970" class="Bound">q</a> <a id="14972" class="Symbol">:</a> <a id="14974" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="14975" class="Symbol">)</a> <a id="14977" class="Symbol">→</a> <a id="14979" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14968" class="Bound">p</a> <a id="14981" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="14983" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14970" class="Bound">q</a> <a id="14985" class="Symbol">→</a> <a id="14987" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14966" class="Bound">m</a> <a id="14989" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="14991" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14968" class="Bound">p</a> <a id="14993" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="14995" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14966" class="Bound">m</a> <a id="14997" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="14999" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14970" class="Bound">q</a>
<a id="15001" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14951" class="Function">+-monoʳ-≤</a> <a id="15011" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="15019" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15019" class="Bound">p</a> <a id="15021" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15021" class="Bound">q</a> <a id="15023" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15023" class="Bound">p≤q</a>  <a id="15028" class="Symbol">=</a>  <a id="15031" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15023" class="Bound">p≤q</a>
<a id="15035" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14951" class="Function">+-monoʳ-≤</a> <a id="15045" class="Symbol">(</a><a id="15046" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="15050" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15050" class="Bound">m</a><a id="15051" class="Symbol">)</a> <a id="15053" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15053" class="Bound">p</a> <a id="15055" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15055" class="Bound">q</a> <a id="15057" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15057" class="Bound">p≤q</a>  <a id="15062" class="Symbol">=</a>  <a id="15065" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1207" class="InductiveConstructor">s≤s</a> <a id="15069" class="Symbol">(</a><a id="15070" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14951" class="Function">+-monoʳ-≤</a> <a id="15080" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15050" class="Bound">m</a> <a id="15082" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15053" class="Bound">p</a> <a id="15084" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15055" class="Bound">q</a> <a id="15086" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15057" class="Bound">p≤q</a><a id="15089" class="Symbol">)</a>{% endraw %}</pre>
The proof is by induction on the first argument.

+ *Base case*: The first argument is `zero` in which case
  `zero + p ≤ zero + q` simplifies to `p ≤ q`, the evidence
  for which is given by the argument `p≤q`.

+ *Inductive case*: The first argument is `suc m`, in which case
  `suc m + p ≤ suc m + q` simplifies to `suc (m + p) ≤ suc (m + q)`.
  The inductive hypothesis `+-monoʳ-≤ m p q p≤q` establishes that
  `m + p ≤ m + q`, and our goal follows by applying `s≤s`.

Second, we deal with the special case of showing addition is
monotonic on the left. This follows from the previous
result and the commutativity of addition.
<pre class="Agda">{% raw %}<a id="+-monoˡ-≤"></a><a id="15746" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15746" class="Function">+-monoˡ-≤</a> <a id="15756" class="Symbol">:</a> <a id="15758" class="Symbol">∀</a> <a id="15760" class="Symbol">(</a><a id="15761" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15761" class="Bound">m</a> <a id="15763" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15763" class="Bound">n</a> <a id="15765" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15765" class="Bound">p</a> <a id="15767" class="Symbol">:</a> <a id="15769" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="15770" class="Symbol">)</a> <a id="15772" class="Symbol">→</a> <a id="15774" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15761" class="Bound">m</a> <a id="15776" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="15778" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15763" class="Bound">n</a> <a id="15780" class="Symbol">→</a> <a id="15782" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15761" class="Bound">m</a> <a id="15784" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="15786" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15765" class="Bound">p</a> <a id="15788" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="15790" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15763" class="Bound">n</a> <a id="15792" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="15794" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15765" class="Bound">p</a>
<a id="15796" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15746" class="Function">+-monoˡ-≤</a> <a id="15806" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15806" class="Bound">m</a> <a id="15808" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15808" class="Bound">n</a> <a id="15810" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15810" class="Bound">p</a> <a id="15812" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15812" class="Bound">m≤n</a> <a id="15816" class="Keyword">rewrite</a> <a id="15824" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#8101" class="Function">+-comm</a> <a id="15831" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15806" class="Bound">m</a> <a id="15833" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15810" class="Bound">p</a> <a id="15835" class="Symbol">|</a> <a id="15837" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#8101" class="Function">+-comm</a> <a id="15844" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15808" class="Bound">n</a> <a id="15846" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15810" class="Bound">p</a> <a id="15848" class="Symbol">=</a> <a id="15850" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14951" class="Function">+-monoʳ-≤</a> <a id="15860" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15810" class="Bound">p</a> <a id="15862" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15806" class="Bound">m</a> <a id="15864" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15808" class="Bound">n</a> <a id="15866" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15812" class="Bound">m≤n</a>{% endraw %}</pre>
Rewriting by `+-comm m p` and `+-comm n p` converts `m + p ≤ n + p` into
`p + m ≤ p + n`, which is proved by invoking `+-monoʳ-≤ p m n m≤n`.

Third, we combine the two previous results.
<pre class="Agda">{% raw %}<a id="+-mono-≤"></a><a id="16080" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16080" class="Function">+-mono-≤</a> <a id="16089" class="Symbol">:</a> <a id="16091" class="Symbol">∀</a> <a id="16093" class="Symbol">(</a><a id="16094" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16094" class="Bound">m</a> <a id="16096" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16096" class="Bound">n</a> <a id="16098" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16098" class="Bound">p</a> <a id="16100" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16100" class="Bound">q</a> <a id="16102" class="Symbol">:</a> <a id="16104" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="16105" class="Symbol">)</a> <a id="16107" class="Symbol">→</a> <a id="16109" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16094" class="Bound">m</a> <a id="16111" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="16113" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16096" class="Bound">n</a> <a id="16115" class="Symbol">→</a> <a id="16117" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16098" class="Bound">p</a> <a id="16119" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="16121" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16100" class="Bound">q</a> <a id="16123" class="Symbol">→</a> <a id="16125" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16094" class="Bound">m</a> <a id="16127" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16129" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16098" class="Bound">p</a> <a id="16131" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">≤</a> <a id="16133" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16096" class="Bound">n</a> <a id="16135" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16137" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16100" class="Bound">q</a>
<a id="16139" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16080" class="Function">+-mono-≤</a> <a id="16148" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16148" class="Bound">m</a> <a id="16150" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16150" class="Bound">n</a> <a id="16152" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16152" class="Bound">p</a> <a id="16154" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16154" class="Bound">q</a> <a id="16156" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16156" class="Bound">m≤n</a> <a id="16160" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16160" class="Bound">p≤q</a> <a id="16164" class="Symbol">=</a> <a id="16166" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#6287" class="Function">≤-trans</a> <a id="16174" class="Symbol">(</a><a id="16175" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#15746" class="Function">+-monoˡ-≤</a> <a id="16185" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16148" class="Bound">m</a> <a id="16187" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16150" class="Bound">n</a> <a id="16189" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16152" class="Bound">p</a> <a id="16191" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16156" class="Bound">m≤n</a><a id="16194" class="Symbol">)</a> <a id="16196" class="Symbol">(</a><a id="16197" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#14951" class="Function">+-monoʳ-≤</a> <a id="16207" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16150" class="Bound">n</a> <a id="16209" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16152" class="Bound">p</a> <a id="16211" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16154" class="Bound">q</a> <a id="16213" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16160" class="Bound">p≤q</a><a id="16216" class="Symbol">)</a>{% endraw %}</pre>
Invoking `+-monoˡ-≤ m n p m≤n` proves `m + p ≤ n + p` and invoking
`+-monoʳ-≤ n p q p≤q` proves `n + p ≤ n + q`, and combining these with
transitivity proves `m + p ≤ n + q`, as was to be shown.


## Strict inequality.

We can define strict inequality similarly to inequality.
<pre class="Agda">{% raw %}<a id="16519" class="Keyword">infix</a> <a id="16525" class="Number">4</a> <a id="16527" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16537" class="Datatype Operator">_&lt;_</a>

<a id="16532" class="Keyword">data</a> <a id="_&lt;_"></a><a id="16537" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16537" class="Datatype Operator">_&lt;_</a> <a id="16541" class="Symbol">:</a> <a id="16543" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="16545" class="Symbol">→</a> <a id="16547" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="16549" class="Symbol">→</a> <a id="16551" class="PrimitiveType">Set</a> <a id="16555" class="Keyword">where</a>
  <a id="_&lt;_.z&lt;s"></a><a id="16563" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16563" class="InductiveConstructor">z&lt;s</a> <a id="16567" class="Symbol">:</a> <a id="16569" class="Symbol">∀</a> <a id="16571" class="Symbol">{</a><a id="16572" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16572" class="Bound">n</a> <a id="16574" class="Symbol">:</a> <a id="16576" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="16577" class="Symbol">}</a> <a id="16579" class="Symbol">→</a> <a id="16581" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="16586" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16537" class="Datatype Operator">&lt;</a> <a id="16588" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="16592" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16572" class="Bound">n</a>
  <a id="_&lt;_.s&lt;s"></a><a id="16596" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16596" class="InductiveConstructor">s&lt;s</a> <a id="16600" class="Symbol">:</a> <a id="16602" class="Symbol">∀</a> <a id="16604" class="Symbol">{</a><a id="16605" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16605" class="Bound">m</a> <a id="16607" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16607" class="Bound">n</a> <a id="16609" class="Symbol">:</a> <a id="16611" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="16612" class="Symbol">}</a> <a id="16614" class="Symbol">→</a> <a id="16616" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16605" class="Bound">m</a> <a id="16618" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16537" class="Datatype Operator">&lt;</a> <a id="16620" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16607" class="Bound">n</a> <a id="16622" class="Symbol">→</a> <a id="16624" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="16628" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16605" class="Bound">m</a> <a id="16630" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16537" class="Datatype Operator">&lt;</a> <a id="16632" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="16636" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#16607" class="Bound">n</a>{% endraw %}</pre>
The key difference is that zero is less than the successor of an
arbitrary number, but is not less than zero.

Clearly, strict inequality is not reflexive. However it is
*irreflexive* in that `n < n` never holds for any value of `n`.
Like inequality, strict inequality is transitive.
Strict inequality is not total, but satisfies the closely related property of
*trichotomy*: for any `m` and `n`, exactly one of `m < n`, `m ≡ n`, or `m > n`
holds (where we define `m > n` to hold exactly where `n < m`).
It is also monotonic with regards to addition and multiplication.

Most of the above are considered in exercises below.  Irreflexivity
requires logical negation, as does the fact that the three cases in
trichotomy are mutually exclusive, so those points are deferred
until the negation is introduced in Chapter [Logic](Logic).

It is straightforward to show that `suc m ≤ n` implies `m < n`,
and conversely.  One can then give an alternative derivation of the
properties of strict inequality, such as transitivity, by directly
exploiting the corresponding properties of inequality.

### Exercise (`<-trans`)

Show that strict inequality is transitive.

### Exercise (`trichotomy`)

Show that strict inequality satisfies a weak version of trichotomy, in the sense
that for any `m` and `n` that one of `m < n`, `m ≡ n`, or `m > n`
holds. You will need to define a suitable data structure, similar
to the one used for totality.  (After negation is introduced in Chapter [Logic](Logic),
we will be in a position to show that the three cases are mutually exclusive.)

### Exercise (`+-mono-<`)

Show that addition is monotonic with respect to strict inequality.
As with inequality, some additional definitions may be required.

### Exercise (`≤-implies-<`, `<-implies-≤`)

Show that `suc m ≤ n` implies `m < n`, and conversely.

### Exercise (`<-trans′`)

Give an alternative proof that strict inequality is transitive,
using the relating between strict inequality and inequality and
the fact that inequality is transitive.


## Even and odd

As a further example, let's specify even and odd numbers.  
Inequality and strict inequality are *binary relations*,
while even and odd are *unary relations*, sometimes called *predicates*.
<pre class="Agda">{% raw %}<a id="18894" class="Keyword">data</a> <a id="even"></a><a id="18899" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18899" class="Datatype">even</a> <a id="18904" class="Symbol">:</a> <a id="18906" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="18908" class="Symbol">→</a> <a id="18910" class="PrimitiveType">Set</a>
<a id="18914" class="Keyword">data</a> <a id="odd"></a><a id="18919" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18919" class="Datatype">odd</a>  <a id="18924" class="Symbol">:</a> <a id="18926" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="18928" class="Symbol">→</a> <a id="18930" class="PrimitiveType">Set</a>

<a id="18935" class="Keyword">data</a> <a id="18940" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18899" class="Datatype">even</a> <a id="18945" class="Keyword">where</a>
  <a id="even.even-zero"></a><a id="18953" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18953" class="InductiveConstructor">even-zero</a> <a id="18963" class="Symbol">:</a> <a id="18965" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18899" class="Datatype">even</a> <a id="18970" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>
  <a id="even.even-suc"></a><a id="18977" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18977" class="InductiveConstructor">even-suc</a>  <a id="18987" class="Symbol">:</a> <a id="18989" class="Symbol">∀</a> <a id="18991" class="Symbol">{</a><a id="18992" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18992" class="Bound">n</a> <a id="18994" class="Symbol">:</a> <a id="18996" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="18997" class="Symbol">}</a> <a id="18999" class="Symbol">→</a> <a id="19001" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18919" class="Datatype">odd</a> <a id="19005" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18992" class="Bound">n</a> <a id="19007" class="Symbol">→</a> <a id="19009" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18899" class="Datatype">even</a> <a id="19014" class="Symbol">(</a><a id="19015" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="19019" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18992" class="Bound">n</a><a id="19020" class="Symbol">)</a>

<a id="19023" class="Keyword">data</a> <a id="19028" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18919" class="Datatype">odd</a> <a id="19032" class="Keyword">where</a>
  <a id="odd.odd-suc"></a><a id="19040" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19040" class="InductiveConstructor">odd-suc</a>   <a id="19050" class="Symbol">:</a> <a id="19052" class="Symbol">∀</a> <a id="19054" class="Symbol">{</a><a id="19055" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19055" class="Bound">n</a> <a id="19057" class="Symbol">:</a> <a id="19059" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="19060" class="Symbol">}</a> <a id="19062" class="Symbol">→</a> <a id="19064" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18899" class="Datatype">even</a> <a id="19069" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19055" class="Bound">n</a> <a id="19071" class="Symbol">→</a> <a id="19073" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18919" class="Datatype">odd</a> <a id="19077" class="Symbol">(</a><a id="19078" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="19082" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19055" class="Bound">n</a><a id="19083" class="Symbol">)</a>{% endraw %}</pre>
A number is even if it is zero or the successor of an odd number,
and odd if it is the successor of an even number.

This is our first use of a mutually recursive datatype declaration.
Since each identifier must be defined before it is used, we first
declare the indexed types `even` and `odd` (omitting the `where`
keyword and the declarations of the constructors) and then
declare the constructors (omitting the signatures `ℕ → Set`
which were given earlier).

We show that the sum of two even numbers is even.
<pre class="Agda">{% raw %}<a id="e+e≡e"></a><a id="19622" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19622" class="Function">e+e≡e</a> <a id="19628" class="Symbol">:</a> <a id="19630" class="Symbol">∀</a> <a id="19632" class="Symbol">{</a><a id="19633" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19633" class="Bound">m</a> <a id="19635" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19635" class="Bound">n</a> <a id="19637" class="Symbol">:</a> <a id="19639" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="19640" class="Symbol">}</a> <a id="19642" class="Symbol">→</a> <a id="19644" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18899" class="Datatype">even</a> <a id="19649" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19633" class="Bound">m</a> <a id="19651" class="Symbol">→</a> <a id="19653" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18899" class="Datatype">even</a> <a id="19658" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19635" class="Bound">n</a> <a id="19660" class="Symbol">→</a> <a id="19662" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18899" class="Datatype">even</a> <a id="19667" class="Symbol">(</a><a id="19668" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19633" class="Bound">m</a> <a id="19670" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="19672" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19635" class="Bound">n</a><a id="19673" class="Symbol">)</a>
<a id="o+e≡o"></a><a id="19675" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19675" class="Function">o+e≡o</a> <a id="19681" class="Symbol">:</a> <a id="19683" class="Symbol">∀</a> <a id="19685" class="Symbol">{</a><a id="19686" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19686" class="Bound">m</a> <a id="19688" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19688" class="Bound">n</a> <a id="19690" class="Symbol">:</a> <a id="19692" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="19693" class="Symbol">}</a> <a id="19695" class="Symbol">→</a> <a id="19697" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18919" class="Datatype">odd</a>  <a id="19702" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19686" class="Bound">m</a> <a id="19704" class="Symbol">→</a> <a id="19706" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18899" class="Datatype">even</a> <a id="19711" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19688" class="Bound">n</a> <a id="19713" class="Symbol">→</a> <a id="19715" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18919" class="Datatype">odd</a>  <a id="19720" class="Symbol">(</a><a id="19721" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19686" class="Bound">m</a> <a id="19723" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="19725" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19688" class="Bound">n</a><a id="19726" class="Symbol">)</a>

<a id="19729" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19622" class="Function">e+e≡e</a> <a id="19735" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18953" class="InductiveConstructor">even-zero</a>     <a id="19749" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19749" class="Bound">en</a>  <a id="19753" class="Symbol">=</a>  <a id="19756" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19749" class="Bound">en</a>
<a id="19759" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19622" class="Function">e+e≡e</a> <a id="19765" class="Symbol">(</a><a id="19766" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18977" class="InductiveConstructor">even-suc</a> <a id="19775" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19775" class="Bound">om</a><a id="19777" class="Symbol">)</a> <a id="19779" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19779" class="Bound">en</a>  <a id="19783" class="Symbol">=</a>  <a id="19786" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#18977" class="InductiveConstructor">even-suc</a> <a id="19795" class="Symbol">(</a><a id="19796" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19675" class="Function">o+e≡o</a> <a id="19802" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19775" class="Bound">om</a> <a id="19805" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19779" class="Bound">en</a><a id="19807" class="Symbol">)</a>

<a id="19810" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19675" class="Function">o+e≡o</a> <a id="19816" class="Symbol">(</a><a id="19817" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19040" class="InductiveConstructor">odd-suc</a>  <a id="19826" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19826" class="Bound">em</a><a id="19828" class="Symbol">)</a> <a id="19830" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19830" class="Bound">en</a>  <a id="19834" class="Symbol">=</a>  <a id="19837" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19040" class="InductiveConstructor">odd-suc</a>  <a id="19846" class="Symbol">(</a><a id="19847" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19622" class="Function">e+e≡e</a> <a id="19853" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19826" class="Bound">em</a> <a id="19856" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#19830" class="Bound">en</a><a id="19858" class="Symbol">)</a>{% endraw %}</pre>
Corresponding to the mutually recursive types, we use two mutually recursive
functions, one to show that the sum of two even numbers is even, and the other
to show that the sum of an odd and an even number is odd.

To show that the sum of two even numbers is even, consider the evidence that the
first number is even. If it because it is zero, then the sum is even because the
second number is even.  If it is because it is the successor of an odd number,
then the result is even because it is the successor of the sum of an odd and an
even number, which is odd.

To show that the sum of an odd and even number is odd, consider the evidence
that the first number is odd. If it is because it is the successor of an even
number, then the result is odd because it is the successor of the sum of two
even numbers, which is even.

This is our first use of mutually recursive functions.  Since each identifier
must be defined before it is used, we first give the signatures for both
functions and then the equations that define them.

### Exercise (`o+o≡e`)

Show that the sum of two odd numbers is even.


## Formalising preorder

<pre class="Agda">{% raw %}<a id="21010" class="Keyword">record</a> <a id="IsPreorder"></a><a id="21017" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21017" class="Record">IsPreorder</a> <a id="21028" class="Symbol">{</a><a id="21029" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21029" class="Bound">A</a> <a id="21031" class="Symbol">:</a> <a id="21033" class="PrimitiveType">Set</a><a id="21036" class="Symbol">}</a> <a id="21038" class="Symbol">(</a><a id="21039" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21039" class="Bound Operator">_≤_</a> <a id="21043" class="Symbol">:</a> <a id="21045" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21029" class="Bound">A</a> <a id="21047" class="Symbol">→</a> <a id="21049" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21029" class="Bound">A</a> <a id="21051" class="Symbol">→</a> <a id="21053" class="PrimitiveType">Set</a><a id="21056" class="Symbol">)</a> <a id="21058" class="Symbol">:</a> <a id="21060" class="PrimitiveType">Set</a> <a id="21064" class="Keyword">where</a>
  <a id="21072" class="Keyword">field</a>
    <a id="IsPreorder.reflexive"></a><a id="21082" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21082" class="Field">reflexive</a> <a id="21092" class="Symbol">:</a> <a id="21094" class="Symbol">∀</a> <a id="21096" class="Symbol">{</a><a id="21097" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21097" class="Bound">x</a> <a id="21099" class="Symbol">:</a> <a id="21101" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21029" class="Bound">A</a><a id="21102" class="Symbol">}</a> <a id="21104" class="Symbol">→</a> <a id="21106" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21097" class="Bound">x</a> <a id="21108" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21039" class="Bound Operator">≤</a> <a id="21110" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21097" class="Bound">x</a>
    <a id="IsPreorder.trans"></a><a id="21116" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21116" class="Field">trans</a> <a id="21122" class="Symbol">:</a> <a id="21124" class="Symbol">∀</a> <a id="21126" class="Symbol">{</a><a id="21127" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21127" class="Bound">x</a> <a id="21129" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21129" class="Bound">y</a> <a id="21131" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21131" class="Bound">z</a> <a id="21133" class="Symbol">:</a> <a id="21135" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21029" class="Bound">A</a><a id="21136" class="Symbol">}</a> <a id="21138" class="Symbol">→</a> <a id="21140" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21127" class="Bound">x</a> <a id="21142" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21039" class="Bound Operator">≤</a> <a id="21144" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21129" class="Bound">y</a> <a id="21146" class="Symbol">→</a> <a id="21148" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21129" class="Bound">y</a> <a id="21150" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21039" class="Bound Operator">≤</a> <a id="21152" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21131" class="Bound">z</a> <a id="21154" class="Symbol">→</a> <a id="21156" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21127" class="Bound">x</a> <a id="21158" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21039" class="Bound Operator">≤</a> <a id="21160" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21131" class="Bound">z</a>

<a id="IsPreorder-≤"></a><a id="21163" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21163" class="Function">IsPreorder-≤</a> <a id="21176" class="Symbol">:</a> <a id="21178" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21017" class="Record">IsPreorder</a> <a id="21189" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#1152" class="Datatype Operator">_≤_</a>
<a id="21193" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#21163" class="Function">IsPreorder-≤</a> <a id="21206" class="Symbol">=</a>
  <a id="21210" class="Keyword">record</a>
    <a id="21221" class="Symbol">{</a> <a id="21223" class="Field">reflexive</a> <a id="21233" class="Symbol">=</a> <a id="21235" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#5629" class="Function">≤-refl</a>
    <a id="21246" class="Symbol">;</a> <a id="21248" class="Field">trans</a> <a id="21254" class="Symbol">=</a> <a id="21256" href="{% endraw %}{{ site.baseurl }}{% link out/Relations.md %}{% raw %}#6287" class="Function">≤-trans</a>
    <a id="21268" class="Symbol">}</a>{% endraw %}</pre>



## Standard prelude

Definitions similar to those in this chapter can be found in the standard library.
<pre class="Agda">{% raw %}<a id="21401" class="Keyword">import</a> <a id="21408" href="https://agda.github.io/agda-stdlib/Data.Nat.html" class="Module">Data.Nat</a> <a id="21417" class="Keyword">using</a> <a id="21423" class="Symbol">(</a><a id="21424" href="https://agda.github.io/agda-stdlib/Data.Nat.Base.html#802" class="Datatype Operator">_≤_</a><a id="21427" class="Symbol">;</a> <a id="21429" href="https://agda.github.io/agda-stdlib/Data.Nat.Base.html#833" class="InductiveConstructor">z≤n</a><a id="21432" class="Symbol">;</a> <a id="21434" href="https://agda.github.io/agda-stdlib/Data.Nat.Base.html#875" class="InductiveConstructor">s≤s</a><a id="21437" class="Symbol">)</a>
<a id="21439" class="Keyword">import</a> <a id="21446" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="21466" class="Keyword">using</a> <a id="21472" class="Symbol">(</a><a id="21473" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#1888" class="Function">≤-refl</a><a id="21479" class="Symbol">;</a> <a id="21481" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#2081" class="Function">≤-trans</a><a id="21488" class="Symbol">;</a> <a id="21490" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#1938" class="Function">≤-antisym</a><a id="21499" class="Symbol">;</a> <a id="21501" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#2193" class="Function">≤-total</a><a id="21508" class="Symbol">;</a>
                                  <a id="21544" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#10972" class="Function">+-monoʳ-≤</a><a id="21553" class="Symbol">;</a> <a id="21555" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#10882" class="Function">+-monoˡ-≤</a><a id="21564" class="Symbol">;</a> <a id="21566" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#10726" class="Function">+-mono-≤</a><a id="21574" class="Symbol">)</a>{% endraw %}</pre>
In the standard library, `≤-total` is formalised in terms of disjunction (which
we define in Chapter [Logic](Logic)), and `+-monoʳ-≤`, `+-monoˡ-≤`, `+-mono-≤`
make implicit arguments that here are explicit.

## Unicode

This chapter uses the following unicode.

    ≤  U+2264  LESS-THAN OR EQUAL TO (\<=, \le)
    ≥  U+2265  GREATER-THAN OR EQUAL TO (̄\>=, \ge)
    ˡ  U+02E1  MODIFIER LETTER SMALL L (\^l)
    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)

The commands `\^l` and `\^r` give access to a variety of superscript
leftward and rightward arrows, and also superscript letters `l` and `r`.

