---
title     : "Stlc: The Simply Typed Lambda-Calculus"
layout    : page
permalink : /Stlc
---

The _lambda-calculus_, first published by the logician Alonzo Church in
1932, is a core calculus with only three syntactic constructs:
variables, abstraction, and application.  It embodies the concept of
_functional abstraction_, which shows up in almost every programming
language in some form (as functions, procedures, or methods).
The _simply-typed lambda calculus_ (or STLC) is a variant of the
lambda calculus published by Church in 1940.  It has just the three
constructs above for function types, plus whatever else is required
for base types. Church had a minimal base type with no operations;
we will be slightly more pragmatic and choose booleans as our base type.

This chapter formalises the STLC (syntax, small-step semantics, and typing rules),
and the next chapter reviews its main properties (progress and preservation).
The new technical challenges arise from the mechanisms of
_variable binding_ and _substitution_.

<!--
We've already seen how to formalize a language with
variables ([Imp]({{ "Imp" | relative_url }})).
There, however, the variables were all global.
In the STLC, we need to handle the variables that name the
parameters to functions, and these are _bound_ variables.
Moreover, instead of just looking up variables in a global store,
we'll need to reduce function applications by _substituting_
arguments for parameters in function bodies.
-->

We choose booleans as our base type for simplicity.  At the end of the
chapter we'll see how to add numbers as a base type, and in later
chapters we'll enrich STLC with useful constructs like pairs, sums,
lists, records, subtyping, and mutable state.

## Imports

<pre class="Agda">{% raw %}<a id="1756" class="Keyword">open</a> <a id="1761" class="Keyword">import</a> <a id="1768" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}" class="Module">Maps</a> <a id="1773" class="Keyword">using</a> <a id="1779" class="Symbol">(</a><a id="1780" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#2171" class="Datatype">Id</a><a id="1782" class="Symbol">;</a> <a id="1784" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#2188" class="InductiveConstructor">id</a><a id="1786" class="Symbol">;</a> <a id="1788" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#2509" class="Function Operator">_≟_</a><a id="1791" class="Symbol">;</a> <a id="1793" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#10132" class="Function">PartialMap</a><a id="1803" class="Symbol">;</a> <a id="1805" class="Keyword">module</a> <a id="1812" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#10221" class="Module">PartialMap</a><a id="1822" class="Symbol">)</a>
<a id="1824" class="Keyword">open</a> <a id="1829" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#10221" class="Module">PartialMap</a> <a id="1840" class="Keyword">using</a> <a id="1846" class="Symbol">(</a><a id="1847" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#10265" class="Function">∅</a><a id="1848" class="Symbol">;</a> <a id="1850" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#11919" class="Function">just-injective</a><a id="1864" class="Symbol">)</a> <a id="1866" class="Keyword">renaming</a> <a id="1875" class="Symbol">(</a><a id="1876" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#10368" class="Function Operator">_,_↦_</a> <a id="1882" class="Symbol">to</a> <a id="1885" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#10368" class="Function Operator">_,_∶_</a><a id="1890" class="Symbol">)</a>
<a id="1892" class="Keyword">open</a> <a id="1897" class="Keyword">import</a> <a id="1904" href="https://agda.github.io/agda-stdlib/Data.Nat.html" class="Module">Data.Nat</a> <a id="1913" class="Keyword">using</a> <a id="1919" class="Symbol">(</a><a id="1920" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="1921" class="Symbol">)</a>
<a id="1923" class="Keyword">open</a> <a id="1928" class="Keyword">import</a> <a id="1935" href="https://agda.github.io/agda-stdlib/Data.Maybe.html" class="Module">Data.Maybe</a> <a id="1946" class="Keyword">using</a> <a id="1952" class="Symbol">(</a><a id="1953" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#335" class="Datatype">Maybe</a><a id="1958" class="Symbol">;</a> <a id="1960" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1603" class="InductiveConstructor">just</a><a id="1964" class="Symbol">;</a> <a id="1966" href="https://agda.github.io/agda-stdlib/Data.Maybe.html#1664" class="InductiveConstructor">nothing</a><a id="1973" class="Symbol">)</a>
<a id="1975" class="Keyword">open</a> <a id="1980" class="Keyword">import</a> <a id="1987" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="2004" class="Keyword">using</a> <a id="2010" class="Symbol">(</a><a id="2011" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#534" class="Datatype">Dec</a><a id="2014" class="Symbol">;</a> <a id="2016" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#570" class="InductiveConstructor">yes</a><a id="2019" class="Symbol">;</a> <a id="2021" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#597" class="InductiveConstructor">no</a><a id="2023" class="Symbol">;</a> <a id="2025" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#464" class="Function Operator">¬_</a><a id="2027" class="Symbol">)</a>
<a id="2029" class="Keyword">open</a> <a id="2034" class="Keyword">import</a> <a id="2041" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="2079" class="Keyword">using</a> <a id="2085" class="Symbol">(</a><a id="2086" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">_≡_</a><a id="2089" class="Symbol">;</a> <a id="2091" href="https://agda.github.io/agda-stdlib/Relation.Binary.Core.html#4493" class="Function Operator">_≢_</a><a id="2094" class="Symbol">;</a> <a id="2096" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="2100" class="Symbol">)</a>{% endraw %}</pre>

## Syntax

We have just two types.

  * Functions, `A ⇒ B`
  * Booleans, `𝔹`

We require some form of base type, because otherwise the set of types
would be empty. Church used a trivial base type `o` with no operations.
For us, it is more convenient to use booleans. Later we will consider
numbers as a base type.

Here is the syntax of types in BNF.

    A, B, C  ::=  A ⇒ B | 𝔹

And here it is formalised in Agda.

<pre class="Agda">{% raw %}<a id="2544" class="Keyword">infixr</a> <a id="2551" class="Number">20</a> <a id="2554" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2583" class="InductiveConstructor Operator">_⇒_</a>

<a id="2559" class="Keyword">data</a> <a id="Type"></a><a id="2564" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2564" class="Datatype">Type</a> <a id="2569" class="Symbol">:</a> <a id="2571" class="PrimitiveType">Set</a> <a id="2575" class="Keyword">where</a>
  <a id="Type._⇒_"></a><a id="2583" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2583" class="InductiveConstructor Operator">_⇒_</a> <a id="2587" class="Symbol">:</a> <a id="2589" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2564" class="Datatype">Type</a> <a id="2594" class="Symbol">→</a> <a id="2596" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2564" class="Datatype">Type</a> <a id="2601" class="Symbol">→</a> <a id="2603" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2564" class="Datatype">Type</a>
  <a id="Type.𝔹"></a><a id="2610" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="2612" class="Symbol">:</a> <a id="2614" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2564" class="Datatype">Type</a>{% endraw %}</pre>

Terms have six constructs. Three are for the core lambda calculus:

  * Variables, `` ` x ``
  * Abstractions, `λ[ x ∶ A ] N`
  * Applications, `L · M`

and three are for the base type, booleans:

  * True, `true`
  * False, `false`
  * Conditions, `if L then M else N`

Abstraction is also called lambda abstraction, and is the construct
from which the calculus takes its name. 

With the exception of variables, each term form either constructs
a value of a given type (abstractions yield functions, true and
false yield booleans) or deconstructs it (applications use functions,
conditionals use booleans). We will see this again when we come
to the rules for assigning types to terms, where constructors
correspond to introduction rules and deconstructors to eliminators.

Here is the syntax of terms in BNF.

    L, M, N  ::=  ` x | λ[ x ∶ A ] N | L · M | true | false | if L then M else N

And here it is formalised in Agda.

<pre class="Agda">{% raw %}<a id="3575" class="Keyword">infixl</a> <a id="3582" class="Number">20</a> <a id="3585" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">_·_</a>
<a id="3589" class="Keyword">infix</a>  <a id="3596" class="Number">15</a> <a id="3599" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[_∶_]_</a>
<a id="3607" class="Keyword">infix</a>  <a id="3614" class="Number">15</a> <a id="3617" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">if_then_else_</a>

<a id="3632" class="Keyword">data</a> <a id="Term"></a><a id="3637" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a> <a id="3642" class="Symbol">:</a> <a id="3644" class="PrimitiveType">Set</a> <a id="3648" class="Keyword">where</a>
  <a id="Term.`"></a><a id="3656" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="3658" class="Symbol">:</a> <a id="3660" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#2171" class="Datatype">Id</a> <a id="3663" class="Symbol">→</a> <a id="3665" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a>
  <a id="Term.λ[_∶_]_"></a><a id="3672" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[_∶_]_</a> <a id="3680" class="Symbol">:</a> <a id="3682" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#2171" class="Datatype">Id</a> <a id="3685" class="Symbol">→</a> <a id="3687" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2564" class="Datatype">Type</a> <a id="3692" class="Symbol">→</a> <a id="3694" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a> <a id="3699" class="Symbol">→</a> <a id="3701" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a>
  <a id="Term._·_"></a><a id="3708" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">_·_</a> <a id="3712" class="Symbol">:</a> <a id="3714" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a> <a id="3719" class="Symbol">→</a> <a id="3721" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a> <a id="3726" class="Symbol">→</a> <a id="3728" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a>
  <a id="Term.true"></a><a id="3735" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a> <a id="3740" class="Symbol">:</a> <a id="3742" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a>
  <a id="Term.false"></a><a id="3749" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3749" class="InductiveConstructor">false</a> <a id="3755" class="Symbol">:</a> <a id="3757" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a>
  <a id="Term.if_then_else_"></a><a id="3764" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">if_then_else_</a> <a id="3778" class="Symbol">:</a> <a id="3780" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a> <a id="3785" class="Symbol">→</a> <a id="3787" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a> <a id="3792" class="Symbol">→</a> <a id="3794" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a> <a id="3799" class="Symbol">→</a> <a id="3801" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a>{% endraw %}</pre>

#### Special characters

We use the following special characters

    ⇒  U+21D2: RIGHTWARDS DOUBLE ARROW (\=>)
    `  U+0060: GRAVE ACCENT 
    λ  U+03BB: GREEK SMALL LETTER LAMBDA (\Gl or \lambda)
    ∶  U+2236: RATIO (\:)
    ·  U+00B7: MIDDLE DOT (\cdot)

Note that ∶ (U+2236 RATIO) is not the same as : (U+003A COLON).
Colon is reserved in Agda for declaring types. Everywhere that we
declare a type in the object language rather than Agda we use
ratio in place of colon.

Using ratio for this purpose is arguably a bad idea, because one must use context
rather than appearance to distinguish it from colon. Arguably, it might be
better to use a different symbol, such as `∈` or `::`.  We reserve `∈`
for use later to indicate that a variable appears free in a term, and
eschew `::` because we consider it too ugly.


#### Formal vs informal

In informal presentation of formal semantics, one uses choice of
variable name to disambiguate and writes `x` rather than `` ` x ``
for a term that is a variable. Agda requires we distinguish.
Often researchers use `var x` rather than `` ` x ``, but we chose
the latter since it is closer to the informal notation `x`.

Similarly, informal presentation often use the notations `A → B` for
functions, `λ x . N` for abstractions, and `L M` for applications.  We
cannot use these, because they overlap with the notation used by Agda.
In `λ[ x ∶ A ] N`, recall that Agda treats square brackets `[]` as
ordinary symbols, while round parentheses `()` and curly braces `{}`
have special meaning.  We would use `L @ M` for application, but
`@` has a reserved meaning in Agda.


#### Examples

Here are a couple of example terms, `not` of type
`𝔹 ⇒ 𝔹`, which complements its argument, and `two` of type
`(𝔹 ⇒ 𝔹) ⇒ 𝔹 ⇒ 𝔹` which takes a function and a boolean
and applies the function to the boolean twice.

<pre class="Agda">{% raw %}<a id="f"></a><a id="5675" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5675" class="Function">f</a> <a id="x"></a><a id="5677" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">x</a> <a id="y"></a><a id="5679" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5679" class="Function">y</a> <a id="5681" class="Symbol">:</a> <a id="5683" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#2171" class="Datatype">Id</a>
<a id="5686" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5675" class="Function">f</a>  <a id="5689" class="Symbol">=</a>  <a id="5692" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#2188" class="InductiveConstructor">id</a> <a id="5695" class="Number">0</a>
<a id="5697" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">x</a>  <a id="5700" class="Symbol">=</a>  <a id="5703" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#2188" class="InductiveConstructor">id</a> <a id="5706" class="Number">1</a>
<a id="5708" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5679" class="Function">y</a>  <a id="5711" class="Symbol">=</a>  <a id="5714" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#2188" class="InductiveConstructor">id</a> <a id="5717" class="Number">2</a>

<a id="not"></a><a id="5720" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5720" class="Function">not</a> <a id="two"></a><a id="5724" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5724" class="Function">two</a> <a id="5728" class="Symbol">:</a> <a id="5730" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a> 
<a id="5736" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5720" class="Function">not</a> <a id="5740" class="Symbol">=</a>  <a id="5743" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[</a> <a id="5746" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">x</a> <a id="5748" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">∶</a> <a id="5750" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="5752" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">]</a> <a id="5754" class="Symbol">(</a><a id="5755" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">if</a> <a id="5758" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="5760" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">x</a> <a id="5762" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">then</a> <a id="5767" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3749" class="InductiveConstructor">false</a> <a id="5773" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">else</a> <a id="5778" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a><a id="5782" class="Symbol">)</a>
<a id="5784" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5724" class="Function">two</a> <a id="5788" class="Symbol">=</a>  <a id="5791" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[</a> <a id="5794" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5675" class="Function">f</a> <a id="5796" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">∶</a> <a id="5798" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="5800" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2583" class="InductiveConstructor Operator">⇒</a> <a id="5802" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="5804" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">]</a> <a id="5806" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[</a> <a id="5809" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">x</a> <a id="5811" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">∶</a> <a id="5813" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="5815" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">]</a> <a id="5817" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="5819" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5675" class="Function">f</a> <a id="5821" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="5823" class="Symbol">(</a><a id="5824" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="5826" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5675" class="Function">f</a> <a id="5828" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="5830" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="5832" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">x</a><a id="5833" class="Symbol">)</a>{% endraw %}</pre>


#### Bound and free variables

In an abstraction `λ[ x ∶ A ] N` we call `x` the _bound_ variable
and `N` the _body_ of the abstraction.  One of the most important
aspects of lambda calculus is that names of bound variables are
irrelevant.  Thus the five terms

* `` λ[ f ∶ 𝔹 ⇒ 𝔹 ] λ[ x ∶ 𝔹 ] ` f · (` f · ` x) ``
* `` λ[ g ∶ 𝔹 ⇒ 𝔹 ] λ[ y ∶ 𝔹 ] ` g · (` g · ` y) ``
* `` λ[ fred ∶ 𝔹 ⇒ 𝔹 ] λ[ xander ∶ 𝔹 ] ` fred · (` fred · ` xander) ``
* `` λ[ 😇 ∶ 𝔹 ⇒ 𝔹 ] λ[ 😈  ∶ 𝔹 ] ` 😇 · (` 😇 · ` 😈 ) ``  
* `` λ[ x ∶ 𝔹 ⇒ 𝔹 ] λ[ f ∶ 𝔹 ] ` x · (` x · ` f) ``

are all considered equivalent.  This equivalence relation
is sometimes called _alpha renaming_.

As we descend from a term into its subterms, variables
that are bound may become free.  Consider the following terms.




* `` λ[ f ∶ 𝔹 ⇒ 𝔹 ] λ[ x ∶ 𝔹 ] ` f · (` f · ` x) ``
  Both variable `f` and `x` are bound.

* `` λ[ x ∶ 𝔹 ] ` f · (` f · ` x) ``
  has `x` as a bound variable but `f` as a free variable.  

* `` ` f · (` f · ` x) ``
  has both `f` and `x` as free variables.

We say that a term with no free variables is _closed_; otherwise it is
_open_.  Of the three terms above, the first is closed and the other
two are open.  A formal definition of bound and free variables will be
given in the next chapter.

Different occurrences of a variable may be bound and free.
In the term 

    (λ[ x ∶ 𝔹 ] ` x) · ` x

the inner occurrence of `x` is bound while the outer occurrence is free.
Note that by alpha renaming, the term above is equivalent to

    (λ[ y ∶ 𝔹 ] ` y) · ` x

in which `y` is bound and `x` is free.  A common convention, called the
Barendregt convention, is to use alpha renaming to ensure that the bound
variables in a term are distinct from the free variables, which can
avoid confusions that may arise if bound and free variables have the
same names.

#### Special characters

    😇  U+1F607: SMILING FACE WITH HALO
    😈  U+1F608: SMILING FACE WITH HORNS

#### Precedence

As in Agda, functions of two or more arguments are represented via
currying. This is made more convenient by declaring `_⇒_` to
associate to the right and `_·_` to associate to the left.
Thus,

* `(𝔹 ⇒ 𝔹) ⇒ 𝔹 ⇒ 𝔹` abbreviates `(𝔹 ⇒ 𝔹) ⇒ (𝔹 ⇒ 𝔹)`
* `two · not · true` abbreviates `(two · not) · true`.

We choose the binding strength for abstractions and conditionals
to be weaker than application. For instance,

* `` λ[ f ∶ 𝔹 ⇒ 𝔹 ] λ[ x ∶ 𝔹 ] ` f · (` f · ` x) ``
  - abbreviates `` (λ[ f ∶ 𝔹 ⇒ 𝔹 ] (λ[ x ∶ 𝔹 ] (` f · (` f · ` x)))) ``
  - and not `` (λ[ f ∶ 𝔹 ⇒ 𝔹 ] (λ[ x ∶ 𝔹 ] ` f)) · (` f · ` x) ``.

<pre class="Agda">{% raw %}<a id="ex₁"></a><a id="8409" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#8409" class="Function">ex₁</a> <a id="8413" class="Symbol">:</a> <a id="8415" class="Symbol">(</a><a id="8416" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="8418" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2583" class="InductiveConstructor Operator">⇒</a> <a id="8420" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a><a id="8421" class="Symbol">)</a> <a id="8423" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2583" class="InductiveConstructor Operator">⇒</a> <a id="8425" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="8427" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2583" class="InductiveConstructor Operator">⇒</a> <a id="8429" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="8431" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="8433" class="Symbol">(</a><a id="8434" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="8436" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2583" class="InductiveConstructor Operator">⇒</a> <a id="8438" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a><a id="8439" class="Symbol">)</a> <a id="8441" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2583" class="InductiveConstructor Operator">⇒</a> <a id="8443" class="Symbol">(</a><a id="8444" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="8446" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2583" class="InductiveConstructor Operator">⇒</a> <a id="8448" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a><a id="8449" class="Symbol">)</a>
<a id="8451" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#8409" class="Function">ex₁</a> <a id="8455" class="Symbol">=</a> <a id="8457" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>

<a id="ex₂"></a><a id="8463" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#8463" class="Function">ex₂</a> <a id="8467" class="Symbol">:</a> <a id="8469" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5724" class="Function">two</a> <a id="8473" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="8475" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5720" class="Function">not</a> <a id="8479" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="8481" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a> <a id="8486" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="8488" class="Symbol">(</a><a id="8489" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5724" class="Function">two</a> <a id="8493" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="8495" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5720" class="Function">not</a><a id="8498" class="Symbol">)</a> <a id="8500" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="8502" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a>
<a id="8507" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#8463" class="Function">ex₂</a> <a id="8511" class="Symbol">=</a> <a id="8513" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>

<a id="ex₃"></a><a id="8519" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#8519" class="Function">ex₃</a> <a id="8523" class="Symbol">:</a> <a id="8525" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[</a> <a id="8528" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5675" class="Function">f</a> <a id="8530" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">∶</a> <a id="8532" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="8534" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2583" class="InductiveConstructor Operator">⇒</a> <a id="8536" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="8538" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">]</a> <a id="8540" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[</a> <a id="8543" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">x</a> <a id="8545" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">∶</a> <a id="8547" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="8549" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">]</a> <a id="8551" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="8553" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5675" class="Function">f</a> <a id="8555" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="8557" class="Symbol">(</a><a id="8558" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="8560" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5675" class="Function">f</a> <a id="8562" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="8564" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="8566" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">x</a><a id="8567" class="Symbol">)</a>
      <a id="8575" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="8577" class="Symbol">(</a><a id="8578" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[</a> <a id="8581" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5675" class="Function">f</a> <a id="8583" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">∶</a> <a id="8585" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="8587" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2583" class="InductiveConstructor Operator">⇒</a> <a id="8589" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="8591" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">]</a> <a id="8593" class="Symbol">(</a><a id="8594" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[</a> <a id="8597" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">x</a> <a id="8599" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">∶</a> <a id="8601" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="8603" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">]</a> <a id="8605" class="Symbol">(</a><a id="8606" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="8608" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5675" class="Function">f</a> <a id="8610" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="8612" class="Symbol">(</a><a id="8613" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="8615" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5675" class="Function">f</a> <a id="8617" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="8619" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="8621" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">x</a><a id="8622" class="Symbol">))))</a>
<a id="8627" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#8519" class="Function">ex₃</a> <a id="8631" class="Symbol">=</a> <a id="8633" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>{% endraw %}</pre>

#### Quiz

* What is the type of the following term?

    λ[ f ∶ 𝔹 ⇒ 𝔹 ] ` f · (` f  · true)

  1. `𝔹 ⇒ (𝔹 ⇒ 𝔹)`
  2. `(𝔹 ⇒ 𝔹) ⇒ 𝔹`
  3. `𝔹 ⇒ 𝔹 ⇒ 𝔹`
  4. `𝔹 ⇒ 𝔹`
  5. `𝔹`

  Give more than one answer if appropriate.

* What is the type of the following term?

    (λ[ f ∶ 𝔹 ⇒ 𝔹 ] ` f · (` f  · true)) · not

  1. `𝔹 ⇒ (𝔹 ⇒ 𝔹)`
  2. `(𝔹 ⇒ 𝔹) ⇒ 𝔹`
  3. `𝔹 ⇒ 𝔹 ⇒ 𝔹`
  4. `𝔹 ⇒ 𝔹`
  5. `𝔹`

  Give more than one answer if appropriate.

## Values

We only consider reduction of _closed_ terms,
those that contain no free variables.  We consider
a precise definition of free variables in
[StlcProp]({{ "StlcProp" | relative_url }}).

A term is a value if it is fully reduced.
For booleans, the situation is clear, `true` and
`false` are values, while conditionals are not.
For functions, applications are not values, because
we expect them to further reduce, and variables are
not values, because we focus on closed terms.
Following convention, we treat all abstractions
as values.

The predicate `Value M` holds if term `M` is a value.

<pre class="Agda">{% raw %}<a id="9694" class="Keyword">data</a> <a id="Value"></a><a id="9699" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#9699" class="Datatype">Value</a> <a id="9705" class="Symbol">:</a> <a id="9707" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a> <a id="9712" class="Symbol">→</a> <a id="9714" class="PrimitiveType">Set</a> <a id="9718" class="Keyword">where</a>
  <a id="Value.value-λ"></a><a id="9726" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#9726" class="InductiveConstructor">value-λ</a>     <a id="9738" class="Symbol">:</a> <a id="9740" class="Symbol">∀</a> <a id="9742" class="Symbol">{</a><a id="9743" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#9743" class="Bound">x</a> <a id="9745" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#9745" class="Bound">A</a> <a id="9747" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#9747" class="Bound">N</a><a id="9748" class="Symbol">}</a> <a id="9750" class="Symbol">→</a> <a id="9752" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#9699" class="Datatype">Value</a> <a id="9758" class="Symbol">(</a><a id="9759" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[</a> <a id="9762" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#9743" class="Bound">x</a> <a id="9764" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">∶</a> <a id="9766" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#9745" class="Bound">A</a> <a id="9768" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">]</a> <a id="9770" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#9747" class="Bound">N</a><a id="9771" class="Symbol">)</a>
  <a id="Value.value-true"></a><a id="9775" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#9775" class="InductiveConstructor">value-true</a>  <a id="9787" class="Symbol">:</a> <a id="9789" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#9699" class="Datatype">Value</a> <a id="9795" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a>
  <a id="Value.value-false"></a><a id="9802" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#9802" class="InductiveConstructor">value-false</a> <a id="9814" class="Symbol">:</a> <a id="9816" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#9699" class="Datatype">Value</a> <a id="9822" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3749" class="InductiveConstructor">false</a>{% endraw %}</pre>

We let `V` and `W` range over values.


#### Formal vs informal

In informal presentations of formal semantics, using
`V` as the name of a metavariable is sufficient to
indicate that it is a value. In Agda, we must explicitly
invoke the `Value` predicate.

#### Other approaches

An alternative is not to focus on closed terms,
to treat variables as values, and to treat
`λ[ x ∶ A ] N` as a value only if `N` is a value.
Indeed, this is how Agda normalises terms.
Formalising this approach requires a more sophisticated
definition of substitution.  Here we only
substitute closed terms for variables, while
the alternative requires the ability to substitute
open terms for variables.

## Substitution

The heart of lambda calculus is the operation of
substituting one term for a variable in another term.
Substitution plays a key role in defining the
operational semantics of function application.
For instance, we have

      (λ[ f ∶ 𝔹 ⇒ 𝔹 ] `f · (`f · true)) · not
    ⟹
      not · (not · true)

where we substitute `not` for `` `f `` in the body
of the function abstraction.

We write substitution as `N [ x := V ]`, meaning
substitute term `V` for free occurrences of variable `x` in term `N`,
or, more compactly, substitute `V` for `x` in `N`.
Substitution works if `V` is any closed term;
it need not be a value, but we use `V` since we
always substitute values.

Here are some examples.

* `` ` f [ f := not ] `` yields `` not ``
* `` true [ f := not ] `` yields `` true ``
* `` (` f · true) [ f := not ] `` yields `` not · true ``
* `` (` f · (` f · true)) [ f := not ] `` yields `` not · (not · true) ``
* `` (λ[ x ∶ 𝔹 ] ` f · (` f · ` x)) [ f := not ] `` yields `` λ[ x ∶ 𝔹 ] not · (not · ` x) ``
* `` (λ[ y ∶ 𝔹 ] ` y) [ x := true ] `` yields `` λ[ y ∶ 𝔹 ] ` y ``
* `` (λ[ x ∶ 𝔹 ] ` x) [ x := true ] `` yields `` λ[ x ∶ 𝔹 ] ` x ``

The last example is important: substituting `true` for `x` in
`` (λ[ x ∶ 𝔹 ] ` x) `` does _not_ yield `` (λ[ x ∶ 𝔹 ] true) ``.
The reason for this is that `x` in the body of `` (λ[ x ∶ 𝔹 ] ` x) ``
is _bound_ by the abstraction.  An important feature of abstraction
is that the choice of bound names is irrelevant: both
`` (λ[ x ∶ 𝔹 ] ` x) `` and `` (λ[ y ∶ 𝔹 ] ` y) `` stand for the
identity function.  The way to think of this is that `x` within
the body of the abstraction stands for a _different_ variable than
`x` outside the abstraction, they both just happen to have the same
name.

Here is the formal definition in Agda.

<pre class="Agda">{% raw %}<a id="_[_:=_]"></a><a id="12325" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">_[_:=_]</a> <a id="12333" class="Symbol">:</a> <a id="12335" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a> <a id="12340" class="Symbol">→</a> <a id="12342" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#2171" class="Datatype">Id</a> <a id="12345" class="Symbol">→</a> <a id="12347" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a> <a id="12352" class="Symbol">→</a> <a id="12354" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a>
<a id="12359" class="Symbol">(</a><a id="12360" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="12362" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12362" class="Bound">x′</a><a id="12364" class="Symbol">)</a> <a id="12366" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">[</a> <a id="12368" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12368" class="Bound">x</a> <a id="12370" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">:=</a> <a id="12373" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12373" class="Bound">V</a> <a id="12375" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">]</a> <a id="12377" class="Keyword">with</a> <a id="12382" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12368" class="Bound">x</a> <a id="12384" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#2509" class="Function Operator">≟</a> <a id="12386" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12362" class="Bound">x′</a>
<a id="12389" class="Symbol">...</a> <a id="12393" class="Symbol">|</a> <a id="12395" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#570" class="InductiveConstructor">yes</a> <a id="12399" class="Symbol">_</a> <a id="12401" class="Symbol">=</a> <a id="12403" class="Bound">V</a>
<a id="12405" class="Symbol">...</a> <a id="12409" class="Symbol">|</a> <a id="12411" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#597" class="InductiveConstructor">no</a>  <a id="12415" class="Symbol">_</a> <a id="12417" class="Symbol">=</a> <a id="12419" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="12421" class="Bound">x′</a>
<a id="12424" class="Symbol">(</a><a id="12425" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[</a> <a id="12428" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12428" class="Bound">x′</a> <a id="12431" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">∶</a> <a id="12433" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12433" class="Bound">A′</a> <a id="12436" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">]</a> <a id="12438" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12438" class="Bound">N′</a><a id="12440" class="Symbol">)</a> <a id="12442" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">[</a> <a id="12444" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12444" class="Bound">x</a> <a id="12446" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">:=</a> <a id="12449" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12449" class="Bound">V</a> <a id="12451" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">]</a> <a id="12453" class="Keyword">with</a> <a id="12458" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12444" class="Bound">x</a> <a id="12460" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#2509" class="Function Operator">≟</a> <a id="12462" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12428" class="Bound">x′</a>
<a id="12465" class="Symbol">...</a> <a id="12469" class="Symbol">|</a> <a id="12471" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#570" class="InductiveConstructor">yes</a> <a id="12475" class="Symbol">_</a> <a id="12477" class="Symbol">=</a> <a id="12479" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[</a> <a id="12482" class="Bound">x′</a> <a id="12485" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">∶</a> <a id="12487" class="Bound">A′</a> <a id="12490" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">]</a> <a id="12492" class="Bound">N′</a>
<a id="12495" class="Symbol">...</a> <a id="12499" class="Symbol">|</a> <a id="12501" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#597" class="InductiveConstructor">no</a>  <a id="12505" class="Symbol">_</a> <a id="12507" class="Symbol">=</a> <a id="12509" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[</a> <a id="12512" class="Bound">x′</a> <a id="12515" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">∶</a> <a id="12517" class="Bound">A′</a> <a id="12520" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">]</a> <a id="12522" class="Symbol">(</a><a id="12523" class="Bound">N′</a> <a id="12526" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">[</a> <a id="12528" class="Bound">x</a> <a id="12530" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">:=</a> <a id="12533" class="Bound">V</a> <a id="12535" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">]</a><a id="12536" class="Symbol">)</a>
<a id="12538" class="Symbol">(</a><a id="12539" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12539" class="Bound">L′</a> <a id="12542" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="12544" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12544" class="Bound">M′</a><a id="12546" class="Symbol">)</a> <a id="12548" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">[</a> <a id="12550" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12550" class="Bound">x</a> <a id="12552" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">:=</a> <a id="12555" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12555" class="Bound">V</a> <a id="12557" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">]</a> <a id="12559" class="Symbol">=</a>  <a id="12562" class="Symbol">(</a><a id="12563" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12539" class="Bound">L′</a> <a id="12566" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">[</a> <a id="12568" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12550" class="Bound">x</a> <a id="12570" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">:=</a> <a id="12573" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12555" class="Bound">V</a> <a id="12575" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">]</a><a id="12576" class="Symbol">)</a> <a id="12578" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="12580" class="Symbol">(</a><a id="12581" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12544" class="Bound">M′</a> <a id="12584" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">[</a> <a id="12586" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12550" class="Bound">x</a> <a id="12588" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">:=</a> <a id="12591" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12555" class="Bound">V</a> <a id="12593" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">]</a><a id="12594" class="Symbol">)</a>
<a id="12596" class="Symbol">(</a><a id="12597" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a><a id="12601" class="Symbol">)</a> <a id="12603" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">[</a> <a id="12605" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12605" class="Bound">x</a> <a id="12607" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">:=</a> <a id="12610" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12610" class="Bound">V</a> <a id="12612" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">]</a> <a id="12614" class="Symbol">=</a> <a id="12616" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a>
<a id="12621" class="Symbol">(</a><a id="12622" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3749" class="InductiveConstructor">false</a><a id="12627" class="Symbol">)</a> <a id="12629" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">[</a> <a id="12631" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12631" class="Bound">x</a> <a id="12633" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">:=</a> <a id="12636" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12636" class="Bound">V</a> <a id="12638" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">]</a> <a id="12640" class="Symbol">=</a> <a id="12642" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3749" class="InductiveConstructor">false</a>
<a id="12648" class="Symbol">(</a><a id="12649" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">if</a> <a id="12652" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12652" class="Bound">L′</a> <a id="12655" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">then</a> <a id="12660" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12660" class="Bound">M′</a> <a id="12663" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">else</a> <a id="12668" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12668" class="Bound">N′</a><a id="12670" class="Symbol">)</a> <a id="12672" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">[</a> <a id="12674" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12674" class="Bound">x</a> <a id="12676" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">:=</a> <a id="12679" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12679" class="Bound">V</a> <a id="12681" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">]</a> <a id="12683" class="Symbol">=</a>
  <a id="12687" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">if</a> <a id="12690" class="Symbol">(</a><a id="12691" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12652" class="Bound">L′</a> <a id="12694" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">[</a> <a id="12696" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12674" class="Bound">x</a> <a id="12698" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">:=</a> <a id="12701" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12679" class="Bound">V</a> <a id="12703" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">]</a><a id="12704" class="Symbol">)</a> <a id="12706" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">then</a> <a id="12711" class="Symbol">(</a><a id="12712" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12660" class="Bound">M′</a> <a id="12715" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">[</a> <a id="12717" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12674" class="Bound">x</a> <a id="12719" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">:=</a> <a id="12722" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12679" class="Bound">V</a> <a id="12724" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">]</a><a id="12725" class="Symbol">)</a> <a id="12727" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">else</a> <a id="12732" class="Symbol">(</a><a id="12733" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12668" class="Bound">N′</a> <a id="12736" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">[</a> <a id="12738" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12674" class="Bound">x</a> <a id="12740" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">:=</a> <a id="12743" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12679" class="Bound">V</a> <a id="12745" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">]</a><a id="12746" class="Symbol">)</a>{% endraw %}</pre>

The two key cases are variables and abstraction.

* For variables, we compare `x`, the variable we are substituting for,
with `x′`, the variable in the term. If they are the same,
we yield `V`, otherwise we yield `x′` unchanged.

* For abstractions, we compare `x`, the variable we are substituting for,
with `x′`, the variable bound in the abstraction. If they are the same,
we yield abstraction unchanged, otherwise we subsititute inside the body.

In all other cases, we push substitution recursively into
the subterms.

#### Special characters

    ′  U+2032: PRIME (\')

Note that ′ (U+2032: PRIME) is not the same as ' (U+0027: APOSTROPHE).


#### Examples

Here is confirmation that the examples above are correct.

<pre class="Agda">{% raw %}<a id="ex₁₁"></a><a id="13496" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#13496" class="Function">ex₁₁</a> <a id="13501" class="Symbol">:</a> <a id="13503" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="13505" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5675" class="Function">f</a> <a id="13507" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">[</a> <a id="13509" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5675" class="Function">f</a> <a id="13511" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">:=</a> <a id="13514" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5720" class="Function">not</a> <a id="13518" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">]</a> <a id="13520" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a>  <a id="13523" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5720" class="Function">not</a>
<a id="13527" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#13496" class="Function">ex₁₁</a> <a id="13532" class="Symbol">=</a> <a id="13534" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>

<a id="ex₁₂"></a><a id="13540" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#13540" class="Function">ex₁₂</a> <a id="13545" class="Symbol">:</a> <a id="13547" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a> <a id="13552" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">[</a> <a id="13554" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5675" class="Function">f</a> <a id="13556" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">:=</a> <a id="13559" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5720" class="Function">not</a> <a id="13563" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">]</a> <a id="13565" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="13567" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a>
<a id="13572" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#13540" class="Function">ex₁₂</a> <a id="13577" class="Symbol">=</a> <a id="13579" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>

<a id="ex₁₃"></a><a id="13585" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#13585" class="Function">ex₁₃</a> <a id="13590" class="Symbol">:</a> <a id="13592" class="Symbol">(</a><a id="13593" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="13595" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5675" class="Function">f</a> <a id="13597" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="13599" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a><a id="13603" class="Symbol">)</a> <a id="13605" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">[</a> <a id="13607" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5675" class="Function">f</a> <a id="13609" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">:=</a> <a id="13612" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5720" class="Function">not</a> <a id="13616" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">]</a> <a id="13618" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="13620" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5720" class="Function">not</a> <a id="13624" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="13626" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a>
<a id="13631" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#13585" class="Function">ex₁₃</a> <a id="13636" class="Symbol">=</a> <a id="13638" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>

<a id="ex₁₄"></a><a id="13644" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#13644" class="Function">ex₁₄</a> <a id="13649" class="Symbol">:</a> <a id="13651" class="Symbol">(</a><a id="13652" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="13654" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5675" class="Function">f</a> <a id="13656" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="13658" class="Symbol">(</a><a id="13659" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="13661" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5675" class="Function">f</a> <a id="13663" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="13665" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a><a id="13669" class="Symbol">))</a> <a id="13672" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">[</a> <a id="13674" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5675" class="Function">f</a> <a id="13676" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">:=</a> <a id="13679" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5720" class="Function">not</a> <a id="13683" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">]</a> <a id="13685" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="13687" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5720" class="Function">not</a> <a id="13691" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="13693" class="Symbol">(</a><a id="13694" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5720" class="Function">not</a> <a id="13698" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="13700" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a><a id="13704" class="Symbol">)</a>
<a id="13706" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#13644" class="Function">ex₁₄</a> <a id="13711" class="Symbol">=</a> <a id="13713" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>

<a id="ex₁₅"></a><a id="13719" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#13719" class="Function">ex₁₅</a> <a id="13724" class="Symbol">:</a> <a id="13726" class="Symbol">(</a><a id="13727" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[</a> <a id="13730" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">x</a> <a id="13732" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">∶</a> <a id="13734" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="13736" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">]</a> <a id="13738" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="13740" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5675" class="Function">f</a> <a id="13742" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="13744" class="Symbol">(</a><a id="13745" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="13747" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5675" class="Function">f</a> <a id="13749" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="13751" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="13753" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">x</a><a id="13754" class="Symbol">))</a> <a id="13757" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">[</a> <a id="13759" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5675" class="Function">f</a> <a id="13761" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">:=</a> <a id="13764" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5720" class="Function">not</a> <a id="13768" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">]</a> <a id="13770" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="13772" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[</a> <a id="13775" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">x</a> <a id="13777" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">∶</a> <a id="13779" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="13781" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">]</a> <a id="13783" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5720" class="Function">not</a> <a id="13787" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="13789" class="Symbol">(</a><a id="13790" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5720" class="Function">not</a> <a id="13794" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="13796" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="13798" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">x</a><a id="13799" class="Symbol">)</a>
<a id="13801" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#13719" class="Function">ex₁₅</a> <a id="13806" class="Symbol">=</a> <a id="13808" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>

<a id="ex₁₆"></a><a id="13814" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#13814" class="Function">ex₁₆</a> <a id="13819" class="Symbol">:</a> <a id="13821" class="Symbol">(</a><a id="13822" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[</a> <a id="13825" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5679" class="Function">y</a> <a id="13827" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">∶</a> <a id="13829" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="13831" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">]</a> <a id="13833" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="13835" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5679" class="Function">y</a><a id="13836" class="Symbol">)</a> <a id="13838" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">[</a> <a id="13840" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">x</a> <a id="13842" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">:=</a> <a id="13845" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a> <a id="13850" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">]</a> <a id="13852" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="13854" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[</a> <a id="13857" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5679" class="Function">y</a> <a id="13859" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">∶</a> <a id="13861" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="13863" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">]</a> <a id="13865" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="13867" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5679" class="Function">y</a>
<a id="13869" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#13814" class="Function">ex₁₆</a> <a id="13874" class="Symbol">=</a> <a id="13876" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>

<a id="ex₁₇"></a><a id="13882" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#13882" class="Function">ex₁₇</a> <a id="13887" class="Symbol">:</a> <a id="13889" class="Symbol">(</a><a id="13890" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[</a> <a id="13893" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">x</a> <a id="13895" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">∶</a> <a id="13897" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="13899" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">]</a> <a id="13901" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="13903" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">x</a><a id="13904" class="Symbol">)</a> <a id="13906" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">[</a> <a id="13908" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">x</a> <a id="13910" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">:=</a> <a id="13913" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a> <a id="13918" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">]</a> <a id="13920" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="13922" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[</a> <a id="13925" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">x</a> <a id="13927" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">∶</a> <a id="13929" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="13931" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">]</a> <a id="13933" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="13935" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">x</a>
<a id="13937" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#13882" class="Function">ex₁₇</a> <a id="13942" class="Symbol">=</a> <a id="13944" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>{% endraw %}</pre>

#### Quiz

What is the result of the following substitution?

    (λ[ y ∶ 𝔹 ] ` x · (λ[ x ∶ 𝔹 ] ` x)) [ x := true ]

1. `` (λ[ y ∶ 𝔹 ] ` x · (λ[ x ∶ 𝔹 ] ` x)) ``
2. `` (λ[ y ∶ 𝔹 ] ` x · (λ[ x ∶ 𝔹 ] true)) ``
3. `` (λ[ y ∶ 𝔹 ] true · (λ[ x ∶ 𝔹 ] ` x)) ``
4. `` (λ[ y ∶ 𝔹 ] true · (λ[ x ∶ 𝔹 ] ` true)) ``


## Reduction

We give the reduction rules for call-by-value lambda calculus.  To
reduce an application, first we reduce the left-hand side until it
becomes a value (which must be an abstraction); then we reduce the
right-hand side until it becomes a value; and finally we substitute
the argument for the variable in the abstraction.  To reduce a
conditional, we first reduce the condition until it becomes a value;
if the condition is true the conditional reduces to the first
branch and if false it reduces to the second branch.a

In an informal presentation of the formal semantics, 
the rules for reduction are written as follows.

    L ⟹ L′
    --------------- ξ·₁
    L · M ⟹ L′ · M

    Value V
    M ⟹ M′
    --------------- ξ·₂
    V · M ⟹ V · M′

    Value V
    --------------------------------- βλ·
    (λ[ x ∶ A ] N) · V ⟹ N [ x := V ]

    L ⟹ L′
    ----------------------------------------- ξif
    if L then M else N ⟹ if L′ then M else N

    -------------------------- βif-true
    if true then M else N ⟹ M

    --------------------------- βif-false
    if false then M else N ⟹ N

As we will show later, the rules are deterministic, in that
at most one rule applies to every term.  As we will also show
later, for every well-typed term either a reduction applies
or it is a value.

The rules break into two sorts. Compatibility rules
direct us to reduce some part of a term.
We give them names starting with the Greek letter xi, `ξ`.
Once a term is sufficiently
reduced, it will consist of a constructor and
a deconstructor, in our case `λ` and `·`, or
`if` and `true`, or `if` and `false`.
We give them names starting with the Greek letter beta, `β`,
and indeed such rules are traditionally called beta rules.

Here are the above rules formalised in Agda.

<pre class="Agda">{% raw %}<a id="16058" class="Keyword">infix</a> <a id="16064" class="Number">10</a> <a id="16067" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16078" class="Datatype Operator">_⟹_</a> 

<a id="16073" class="Keyword">data</a> <a id="_⟹_"></a><a id="16078" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16078" class="Datatype Operator">_⟹_</a> <a id="16082" class="Symbol">:</a> <a id="16084" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a> <a id="16089" class="Symbol">→</a> <a id="16091" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a> <a id="16096" class="Symbol">→</a> <a id="16098" class="PrimitiveType">Set</a> <a id="16102" class="Keyword">where</a>
  <a id="_⟹_.ξ·₁"></a><a id="16110" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16110" class="InductiveConstructor">ξ·₁</a> <a id="16114" class="Symbol">:</a> <a id="16116" class="Symbol">∀</a> <a id="16118" class="Symbol">{</a><a id="16119" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16119" class="Bound">L</a> <a id="16121" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16121" class="Bound">L′</a> <a id="16124" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16124" class="Bound">M</a><a id="16125" class="Symbol">}</a> <a id="16127" class="Symbol">→</a>
    <a id="16133" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16119" class="Bound">L</a> <a id="16135" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16078" class="Datatype Operator">⟹</a> <a id="16137" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16121" class="Bound">L′</a> <a id="16140" class="Symbol">→</a>
    <a id="16146" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16119" class="Bound">L</a> <a id="16148" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="16150" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16124" class="Bound">M</a> <a id="16152" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16078" class="Datatype Operator">⟹</a> <a id="16154" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16121" class="Bound">L′</a> <a id="16157" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="16159" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16124" class="Bound">M</a>
  <a id="_⟹_.ξ·₂"></a><a id="16163" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16163" class="InductiveConstructor">ξ·₂</a> <a id="16167" class="Symbol">:</a> <a id="16169" class="Symbol">∀</a> <a id="16171" class="Symbol">{</a><a id="16172" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16172" class="Bound">V</a> <a id="16174" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16174" class="Bound">M</a> <a id="16176" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16176" class="Bound">M′</a><a id="16178" class="Symbol">}</a> <a id="16180" class="Symbol">→</a>
    <a id="16186" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#9699" class="Datatype">Value</a> <a id="16192" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16172" class="Bound">V</a> <a id="16194" class="Symbol">→</a>
    <a id="16200" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16174" class="Bound">M</a> <a id="16202" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16078" class="Datatype Operator">⟹</a> <a id="16204" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16176" class="Bound">M′</a> <a id="16207" class="Symbol">→</a>
    <a id="16213" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16172" class="Bound">V</a> <a id="16215" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="16217" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16174" class="Bound">M</a> <a id="16219" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16078" class="Datatype Operator">⟹</a> <a id="16221" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16172" class="Bound">V</a> <a id="16223" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="16225" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16176" class="Bound">M′</a>
  <a id="_⟹_.βλ·"></a><a id="16230" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16230" class="InductiveConstructor">βλ·</a> <a id="16234" class="Symbol">:</a> <a id="16236" class="Symbol">∀</a> <a id="16238" class="Symbol">{</a><a id="16239" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16239" class="Bound">x</a> <a id="16241" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16241" class="Bound">A</a> <a id="16243" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16243" class="Bound">N</a> <a id="16245" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16245" class="Bound">V</a><a id="16246" class="Symbol">}</a> <a id="16248" class="Symbol">→</a> <a id="16250" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#9699" class="Datatype">Value</a> <a id="16256" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16245" class="Bound">V</a> <a id="16258" class="Symbol">→</a>
    <a id="16264" class="Symbol">(</a><a id="16265" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[</a> <a id="16268" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16239" class="Bound">x</a> <a id="16270" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">∶</a> <a id="16272" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16241" class="Bound">A</a> <a id="16274" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">]</a> <a id="16276" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16243" class="Bound">N</a><a id="16277" class="Symbol">)</a> <a id="16279" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="16281" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16245" class="Bound">V</a> <a id="16283" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16078" class="Datatype Operator">⟹</a> <a id="16285" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16243" class="Bound">N</a> <a id="16287" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">[</a> <a id="16289" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16239" class="Bound">x</a> <a id="16291" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">:=</a> <a id="16294" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16245" class="Bound">V</a> <a id="16296" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#12325" class="Function Operator">]</a>
  <a id="_⟹_.ξif"></a><a id="16300" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16300" class="InductiveConstructor">ξif</a> <a id="16304" class="Symbol">:</a> <a id="16306" class="Symbol">∀</a> <a id="16308" class="Symbol">{</a><a id="16309" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16309" class="Bound">L</a> <a id="16311" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16311" class="Bound">L′</a> <a id="16314" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16314" class="Bound">M</a> <a id="16316" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16316" class="Bound">N</a><a id="16317" class="Symbol">}</a> <a id="16319" class="Symbol">→</a>
    <a id="16325" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16309" class="Bound">L</a> <a id="16327" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16078" class="Datatype Operator">⟹</a> <a id="16329" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16311" class="Bound">L′</a> <a id="16332" class="Symbol">→</a>    
    <a id="16342" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">if</a> <a id="16345" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16309" class="Bound">L</a> <a id="16347" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">then</a> <a id="16352" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16314" class="Bound">M</a> <a id="16354" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">else</a> <a id="16359" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16316" class="Bound">N</a> <a id="16361" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16078" class="Datatype Operator">⟹</a> <a id="16363" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">if</a> <a id="16366" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16311" class="Bound">L′</a> <a id="16369" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">then</a> <a id="16374" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16314" class="Bound">M</a> <a id="16376" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">else</a> <a id="16381" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16316" class="Bound">N</a>
  <a id="_⟹_.βif-true"></a><a id="16385" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16385" class="InductiveConstructor">βif-true</a> <a id="16394" class="Symbol">:</a> <a id="16396" class="Symbol">∀</a> <a id="16398" class="Symbol">{</a><a id="16399" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16399" class="Bound">M</a> <a id="16401" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16401" class="Bound">N</a><a id="16402" class="Symbol">}</a> <a id="16404" class="Symbol">→</a>
    <a id="16410" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">if</a> <a id="16413" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a> <a id="16418" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">then</a> <a id="16423" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16399" class="Bound">M</a> <a id="16425" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">else</a> <a id="16430" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16401" class="Bound">N</a> <a id="16432" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16078" class="Datatype Operator">⟹</a> <a id="16434" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16399" class="Bound">M</a>
  <a id="_⟹_.βif-false"></a><a id="16438" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16438" class="InductiveConstructor">βif-false</a> <a id="16448" class="Symbol">:</a> <a id="16450" class="Symbol">∀</a> <a id="16452" class="Symbol">{</a><a id="16453" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16453" class="Bound">M</a> <a id="16455" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16455" class="Bound">N</a><a id="16456" class="Symbol">}</a> <a id="16458" class="Symbol">→</a>
    <a id="16464" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">if</a> <a id="16467" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3749" class="InductiveConstructor">false</a> <a id="16473" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">then</a> <a id="16478" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16453" class="Bound">M</a> <a id="16480" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">else</a> <a id="16485" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16455" class="Bound">N</a> <a id="16487" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16078" class="Datatype Operator">⟹</a> <a id="16489" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16455" class="Bound">N</a>{% endraw %}</pre>

#### Special characters

We use the following special characters

    ⟹  U+27F9: LONG RIGHTWARDS DOUBLE ARROW (\r6)
    ξ  U+03BE: GREEK SMALL LETTER XI (\Gx or \xi)
    β  U+03B2: GREEK SMALL LETTER BETA (\Gb or \beta)

#### Quiz

What does the following term step to?

    (λ[ x ∶ 𝔹 ⇒ 𝔹 ] ` x) · (λ [ x ∶ 𝔹 ] ` x)  ⟹  ???

1.  `` (λ [ x ∶ 𝔹 ] ` x) ``
2.  `` (λ[ x ∶ 𝔹 ⇒ 𝔹 ] ` x) ``
3.  `` (λ[ x ∶ 𝔹 ⇒ 𝔹 ] ` x) · (λ [ x ∶ 𝔹 ] ` x) ``

What does the following term step to?

    (λ[ x ∶ 𝔹 ⇒ 𝔹 ] ` x) · ((λ[ x ∶ 𝔹 ⇒ 𝔹 ] ` x) (λ [ x ∶ 𝔹 ] ` x))  ⟹  ???

1.  `` (λ [ x ∶ 𝔹 ] ` x) ``
2.  `` (λ[ x ∶ 𝔹 ⇒ 𝔹 ] ` x) ``
3.  `` (λ[ x ∶ 𝔹 ⇒ 𝔹 ] ` x) · (λ [ x ∶ 𝔹 ] ` x) ``

What does the following term step to?  (Where `not` is as defined above.)

    not · true  ⟹  ???

1.  `` if ` x then false else true ``
2.  `` if true then false else true ``
3.  `` true ``
4.  `` false ``

What does the following term step to?  (Where `two` and `not` are as defined above.)

    two · not · true  ⟹  ???

1.  `` not · (not · true) ``
2.  `` (λ[ x ∶ 𝔹 ] not · (not · ` x)) · true ``
4.  `` true ``
5.  `` false ``

## Reflexive and transitive closure

A single step is only part of the story. In general, we wish to repeatedly
step a closed term until it reduces to a value.  We do this by defining
the reflexive and transitive closure `⟹*` of the step function `⟹`.
In an informal presentation of the formal semantics, the rules
are written as follows.

    ------- done
    M ⟹* M

    L ⟹ M
    M ⟹* N
    ------- step
    L ⟹* N

Here it is formalised in Agda.

<pre class="Agda">{% raw %}<a id="18063" class="Keyword">infix</a> <a id="18069" class="Number">10</a> <a id="18072" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18112" class="Datatype Operator">_⟹*_</a> 
<a id="18078" class="Keyword">infixr</a> <a id="18085" class="Number">2</a> <a id="18087" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18165" class="InductiveConstructor Operator">_⟹⟨_⟩_</a>
<a id="18094" class="Keyword">infix</a>  <a id="18101" class="Number">3</a> <a id="18103" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18145" class="InductiveConstructor Operator">_∎</a>

<a id="18107" class="Keyword">data</a> <a id="_⟹*_"></a><a id="18112" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18112" class="Datatype Operator">_⟹*_</a> <a id="18117" class="Symbol">:</a> <a id="18119" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a> <a id="18124" class="Symbol">→</a> <a id="18126" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a> <a id="18131" class="Symbol">→</a> <a id="18133" class="PrimitiveType">Set</a> <a id="18137" class="Keyword">where</a>
  <a id="_⟹*_._∎"></a><a id="18145" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18145" class="InductiveConstructor Operator">_∎</a> <a id="18148" class="Symbol">:</a> <a id="18150" class="Symbol">∀</a> <a id="18152" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18152" class="Bound">M</a> <a id="18154" class="Symbol">→</a> <a id="18156" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18152" class="Bound">M</a> <a id="18158" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18112" class="Datatype Operator">⟹*</a> <a id="18161" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18152" class="Bound">M</a>
  <a id="_⟹*_._⟹⟨_⟩_"></a><a id="18165" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18165" class="InductiveConstructor Operator">_⟹⟨_⟩_</a> <a id="18172" class="Symbol">:</a> <a id="18174" class="Symbol">∀</a> <a id="18176" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18176" class="Bound">L</a> <a id="18178" class="Symbol">{</a><a id="18179" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18179" class="Bound">M</a> <a id="18181" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18181" class="Bound">N</a><a id="18182" class="Symbol">}</a> <a id="18184" class="Symbol">→</a> <a id="18186" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18176" class="Bound">L</a> <a id="18188" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16078" class="Datatype Operator">⟹</a> <a id="18190" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18179" class="Bound">M</a> <a id="18192" class="Symbol">→</a> <a id="18194" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18179" class="Bound">M</a> <a id="18196" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18112" class="Datatype Operator">⟹*</a> <a id="18199" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18181" class="Bound">N</a> <a id="18201" class="Symbol">→</a> <a id="18203" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18176" class="Bound">L</a> <a id="18205" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18112" class="Datatype Operator">⟹*</a> <a id="18208" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18181" class="Bound">N</a>{% endraw %}</pre>

We can read this as follows.

* From term `M`, we can take no steps, giving `M ∎` of type `M ⟹* M`.

* From term `L` we can take a single step `L⟹M` of type `L ⟹ M`
  followed by zero or more steps `M⟹*N` of type `M ⟹* N`,
  giving `L ⟨ L⟹M ⟩ M⟹*N` of type `L ⟹* N`.

The names of the two clauses in the definition of reflexive
and transitive closure have been chosen to allow us to lay
out example reductions in an appealing way.

<pre class="Agda">{% raw %}<a id="reduction₁"></a><a id="18669" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18669" class="Function">reduction₁</a> <a id="18680" class="Symbol">:</a> <a id="18682" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5720" class="Function">not</a> <a id="18686" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="18688" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a> <a id="18693" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18112" class="Datatype Operator">⟹*</a> <a id="18696" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3749" class="InductiveConstructor">false</a>
<a id="18702" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18669" class="Function">reduction₁</a> <a id="18713" class="Symbol">=</a>
    <a id="18719" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5720" class="Function">not</a> <a id="18723" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="18725" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a>
  <a id="18732" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18165" class="InductiveConstructor Operator">⟹⟨</a> <a id="18735" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16230" class="InductiveConstructor">βλ·</a> <a id="18739" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#9775" class="InductiveConstructor">value-true</a> <a id="18750" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18165" class="InductiveConstructor Operator">⟩</a>
    <a id="18756" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">if</a> <a id="18759" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a> <a id="18764" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">then</a> <a id="18769" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3749" class="InductiveConstructor">false</a> <a id="18775" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">else</a> <a id="18780" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a>
  <a id="18787" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18165" class="InductiveConstructor Operator">⟹⟨</a> <a id="18790" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16385" class="InductiveConstructor">βif-true</a> <a id="18799" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18165" class="InductiveConstructor Operator">⟩</a>
    <a id="18805" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3749" class="InductiveConstructor">false</a>
  <a id="18813" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18145" class="InductiveConstructor Operator">∎</a>

<a id="reduction₂"></a><a id="18816" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18816" class="Function">reduction₂</a> <a id="18827" class="Symbol">:</a> <a id="18829" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5724" class="Function">two</a> <a id="18833" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="18835" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5720" class="Function">not</a> <a id="18839" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="18841" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a> <a id="18846" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18112" class="Datatype Operator">⟹*</a> <a id="18849" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a>
<a id="18854" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18816" class="Function">reduction₂</a> <a id="18865" class="Symbol">=</a>
    <a id="18871" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5724" class="Function">two</a> <a id="18875" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="18877" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5720" class="Function">not</a> <a id="18881" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="18883" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a>
  <a id="18890" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18165" class="InductiveConstructor Operator">⟹⟨</a> <a id="18893" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16110" class="InductiveConstructor">ξ·₁</a> <a id="18897" class="Symbol">(</a><a id="18898" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16230" class="InductiveConstructor">βλ·</a> <a id="18902" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#9726" class="InductiveConstructor">value-λ</a><a id="18909" class="Symbol">)</a> <a id="18911" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18165" class="InductiveConstructor Operator">⟩</a>
    <a id="18917" class="Symbol">(</a><a id="18918" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[</a> <a id="18921" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">x</a> <a id="18923" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">∶</a> <a id="18925" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="18927" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">]</a> <a id="18929" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5720" class="Function">not</a> <a id="18933" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="18935" class="Symbol">(</a><a id="18936" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5720" class="Function">not</a> <a id="18940" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="18942" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="18944" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">x</a><a id="18945" class="Symbol">))</a> <a id="18948" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="18950" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a>
  <a id="18957" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18165" class="InductiveConstructor Operator">⟹⟨</a> <a id="18960" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16230" class="InductiveConstructor">βλ·</a> <a id="18964" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#9775" class="InductiveConstructor">value-true</a> <a id="18975" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18165" class="InductiveConstructor Operator">⟩</a>
    <a id="18981" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5720" class="Function">not</a> <a id="18985" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="18987" class="Symbol">(</a><a id="18988" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5720" class="Function">not</a> <a id="18992" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="18994" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a><a id="18998" class="Symbol">)</a>
  <a id="19002" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18165" class="InductiveConstructor Operator">⟹⟨</a> <a id="19005" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16163" class="InductiveConstructor">ξ·₂</a> <a id="19009" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#9726" class="InductiveConstructor">value-λ</a> <a id="19017" class="Symbol">(</a><a id="19018" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16230" class="InductiveConstructor">βλ·</a> <a id="19022" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#9775" class="InductiveConstructor">value-true</a><a id="19032" class="Symbol">)</a> <a id="19034" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18165" class="InductiveConstructor Operator">⟩</a>
    <a id="19040" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5720" class="Function">not</a> <a id="19044" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="19046" class="Symbol">(</a><a id="19047" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">if</a> <a id="19050" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a> <a id="19055" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">then</a> <a id="19060" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3749" class="InductiveConstructor">false</a> <a id="19066" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">else</a> <a id="19071" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a><a id="19075" class="Symbol">)</a>
  <a id="19079" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18165" class="InductiveConstructor Operator">⟹⟨</a> <a id="19082" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16163" class="InductiveConstructor">ξ·₂</a> <a id="19086" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#9726" class="InductiveConstructor">value-λ</a> <a id="19094" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16385" class="InductiveConstructor">βif-true</a>  <a id="19104" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18165" class="InductiveConstructor Operator">⟩</a>
    <a id="19110" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5720" class="Function">not</a> <a id="19114" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="19116" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3749" class="InductiveConstructor">false</a>
  <a id="19124" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18165" class="InductiveConstructor Operator">⟹⟨</a> <a id="19127" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16230" class="InductiveConstructor">βλ·</a> <a id="19131" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#9802" class="InductiveConstructor">value-false</a> <a id="19143" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18165" class="InductiveConstructor Operator">⟩</a>
    <a id="19149" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">if</a> <a id="19152" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3749" class="InductiveConstructor">false</a> <a id="19158" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">then</a> <a id="19163" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3749" class="InductiveConstructor">false</a> <a id="19169" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">else</a> <a id="19174" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a>
  <a id="19181" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18165" class="InductiveConstructor Operator">⟹⟨</a> <a id="19184" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#16438" class="InductiveConstructor">βif-false</a> <a id="19194" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18165" class="InductiveConstructor Operator">⟩</a>
    <a id="19200" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a>
  <a id="19207" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#18145" class="InductiveConstructor Operator">∎</a>{% endraw %}</pre>

Much of the above, though not all, can be filled in using C-c C-r and C-c C-s.

#### Special characters

We use the following special characters

    ∎  U+220E: END OF PROOF (\qed)
    ⟨  U+27E8: MATHEMATICAL LEFT ANGLE BRACKET (\<)
    ⟩  U+27E9: MATHEMATICAL RIGHT ANGLE BRACKET (\>)

## Typing

While reduction considers only closed terms, typing must
consider terms with free variables.  To type a term,
we must first type its subterms, and in particular in the
body of an abstraction its bound variable may appear free.

In general, we use typing _judgements_ of the form

    Γ ⊢ M ∶ A

which asserts in type environment `Γ` that term `M` has type `A`.
Environment `Γ` provides types for all the free variables in `M`.

Here are three examples. 

* `` ∅ , f ∶ 𝔹 ⇒ 𝔹 , x ∶ 𝔹 ⊢ ` f · (` f · ` x) ∶  𝔹 ``
* `` ∅ , f ∶ 𝔹 ⇒ 𝔹 ⊢ (λ[ x ∶ 𝔹 ] ` f · (` f · ` x)) ∶  𝔹 ⇒ 𝔹 ``
* `` ∅ ⊢ (λ[ f ∶ 𝔹 ⇒ 𝔹 ] λ[ x ∶ 𝔹 ] ` f · (` f · ` x)) ∶  (𝔹 ⇒ 𝔹) ⇒ 𝔹 ⇒ 𝔹 ``

Environments are partial maps from identifiers to types, built using `∅`
for the empty map, and `Γ , x ∶ A` for the map that extends
environment `Γ` by mapping variable `x` to type `A`.

In an informal presentation of the formal semantics, 
the rules for typing are written as follows.

    Γ x ≡ A
    ----------- Ax
    Γ ⊢ ` x ∶ A

    Γ , x ∶ A ⊢ N ∶ B
    ------------------------ ⇒-I
    Γ ⊢ λ[ x ∶ A ] N ∶ A ⇒ B

    Γ ⊢ L ∶ A ⇒ B
    Γ ⊢ M ∶ A
    -------------- ⇒-E
    Γ ⊢ L · M ∶ B

    ------------- 𝔹-I₁
    Γ ⊢ true ∶ 𝔹

    -------------- 𝔹-I₂
    Γ ⊢ false ∶ 𝔹

    Γ ⊢ L : 𝔹
    Γ ⊢ M ∶ A
    Γ ⊢ N ∶ A
    -------------------------- 𝔹-E
    Γ ⊢ if L then M else N ∶ A

As we will show later, the rules are deterministic, in that
at most one rule applies to every term. 

The proof rules come in pairs, with rules to introduce and to
eliminate each connective, labeled `-I` and `-E`, respectively. As we
read the rules from top to bottom, introduction and elimination rules
do what they say on the tin: the first _introduces_ a formula for the
connective, which appears in the conclusion but not in the premises;
while the second _eliminates_ a formula for the connective, which appears in
a premise but not in the conclusion. An introduction rule describes
how to construct a value of the type (abstractions yield functions,
true and false yield booleans), while an elimination rule describes
how to deconstruct a value of the given type (applications use
functions, conditionals use booleans).

Here are the above rules formalised in Agda.

<pre class="Agda">{% raw %}<a id="Context"></a><a id="21744" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21744" class="Function">Context</a> <a id="21752" class="Symbol">:</a> <a id="21754" class="PrimitiveType">Set</a>
<a id="21758" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21744" class="Function">Context</a> <a id="21766" class="Symbol">=</a> <a id="21768" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#10132" class="Function">PartialMap</a> <a id="21779" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2564" class="Datatype">Type</a>

<a id="21785" class="Keyword">infix</a> <a id="21791" class="Number">10</a> <a id="21794" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21806" class="Datatype Operator">_⊢_∶_</a>

<a id="21801" class="Keyword">data</a> <a id="_⊢_∶_"></a><a id="21806" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21806" class="Datatype Operator">_⊢_∶_</a> <a id="21812" class="Symbol">:</a> <a id="21814" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21744" class="Function">Context</a> <a id="21822" class="Symbol">→</a> <a id="21824" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3637" class="Datatype">Term</a> <a id="21829" class="Symbol">→</a> <a id="21831" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2564" class="Datatype">Type</a> <a id="21836" class="Symbol">→</a> <a id="21838" class="PrimitiveType">Set</a> <a id="21842" class="Keyword">where</a>
  <a id="_⊢_∶_.Ax"></a><a id="21850" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21850" class="InductiveConstructor">Ax</a> <a id="21853" class="Symbol">:</a> <a id="21855" class="Symbol">∀</a> <a id="21857" class="Symbol">{</a><a id="21858" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21858" class="Bound">Γ</a> <a id="21860" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21860" class="Bound">x</a> <a id="21862" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21862" class="Bound">A</a><a id="21863" class="Symbol">}</a> <a id="21865" class="Symbol">→</a>
    <a id="21871" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21858" class="Bound">Γ</a> <a id="21873" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21860" class="Bound">x</a> <a id="21875" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="21877" href="https://agda.github.io/agda-stdlib/Data.Maybe.Base.html#373" class="InductiveConstructor">just</a> <a id="21882" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21862" class="Bound">A</a> <a id="21884" class="Symbol">→</a>
    <a id="21890" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21858" class="Bound">Γ</a> <a id="21892" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21806" class="Datatype Operator">⊢</a> <a id="21894" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="21896" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21860" class="Bound">x</a> <a id="21898" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21806" class="Datatype Operator">∶</a> <a id="21900" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21862" class="Bound">A</a>
  <a id="_⊢_∶_.⇒-I"></a><a id="21904" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21904" class="InductiveConstructor">⇒-I</a> <a id="21908" class="Symbol">:</a> <a id="21910" class="Symbol">∀</a> <a id="21912" class="Symbol">{</a><a id="21913" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21913" class="Bound">Γ</a> <a id="21915" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21915" class="Bound">x</a> <a id="21917" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21917" class="Bound">N</a> <a id="21919" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21919" class="Bound">A</a> <a id="21921" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21921" class="Bound">B</a><a id="21922" class="Symbol">}</a> <a id="21924" class="Symbol">→</a>
    <a id="21930" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21913" class="Bound">Γ</a> <a id="21932" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#10368" class="Function Operator">,</a> <a id="21934" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21915" class="Bound">x</a> <a id="21936" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#10368" class="Function Operator">∶</a> <a id="21938" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21919" class="Bound">A</a> <a id="21940" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21806" class="Datatype Operator">⊢</a> <a id="21942" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21917" class="Bound">N</a> <a id="21944" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21806" class="Datatype Operator">∶</a> <a id="21946" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21921" class="Bound">B</a> <a id="21948" class="Symbol">→</a>
    <a id="21954" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21913" class="Bound">Γ</a> <a id="21956" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21806" class="Datatype Operator">⊢</a> <a id="21958" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[</a> <a id="21961" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21915" class="Bound">x</a> <a id="21963" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">∶</a> <a id="21965" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21919" class="Bound">A</a> <a id="21967" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">]</a> <a id="21969" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21917" class="Bound">N</a> <a id="21971" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21806" class="Datatype Operator">∶</a> <a id="21973" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21919" class="Bound">A</a> <a id="21975" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2583" class="InductiveConstructor Operator">⇒</a> <a id="21977" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21921" class="Bound">B</a>
  <a id="_⊢_∶_.⇒-E"></a><a id="21981" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21981" class="InductiveConstructor">⇒-E</a> <a id="21985" class="Symbol">:</a> <a id="21987" class="Symbol">∀</a> <a id="21989" class="Symbol">{</a><a id="21990" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21990" class="Bound">Γ</a> <a id="21992" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21992" class="Bound">L</a> <a id="21994" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21994" class="Bound">M</a> <a id="21996" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21996" class="Bound">A</a> <a id="21998" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21998" class="Bound">B</a><a id="21999" class="Symbol">}</a> <a id="22001" class="Symbol">→</a>
    <a id="22007" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21990" class="Bound">Γ</a> <a id="22009" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21806" class="Datatype Operator">⊢</a> <a id="22011" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21992" class="Bound">L</a> <a id="22013" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21806" class="Datatype Operator">∶</a> <a id="22015" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21996" class="Bound">A</a> <a id="22017" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2583" class="InductiveConstructor Operator">⇒</a> <a id="22019" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21998" class="Bound">B</a> <a id="22021" class="Symbol">→</a>
    <a id="22027" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21990" class="Bound">Γ</a> <a id="22029" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21806" class="Datatype Operator">⊢</a> <a id="22031" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21994" class="Bound">M</a> <a id="22033" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21806" class="Datatype Operator">∶</a> <a id="22035" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21996" class="Bound">A</a> <a id="22037" class="Symbol">→</a>
    <a id="22043" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21990" class="Bound">Γ</a> <a id="22045" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21806" class="Datatype Operator">⊢</a> <a id="22047" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21992" class="Bound">L</a> <a id="22049" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="22051" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21994" class="Bound">M</a> <a id="22053" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21806" class="Datatype Operator">∶</a> <a id="22055" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21998" class="Bound">B</a>
  <a id="_⊢_∶_.𝔹-I₁"></a><a id="22059" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22059" class="InductiveConstructor">𝔹-I₁</a> <a id="22064" class="Symbol">:</a> <a id="22066" class="Symbol">∀</a> <a id="22068" class="Symbol">{</a><a id="22069" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22069" class="Bound">Γ</a><a id="22070" class="Symbol">}</a> <a id="22072" class="Symbol">→</a>
    <a id="22078" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22069" class="Bound">Γ</a> <a id="22080" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21806" class="Datatype Operator">⊢</a> <a id="22082" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a> <a id="22087" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21806" class="Datatype Operator">∶</a> <a id="22089" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a>
  <a id="_⊢_∶_.𝔹-I₂"></a><a id="22093" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22093" class="InductiveConstructor">𝔹-I₂</a> <a id="22098" class="Symbol">:</a> <a id="22100" class="Symbol">∀</a> <a id="22102" class="Symbol">{</a><a id="22103" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22103" class="Bound">Γ</a><a id="22104" class="Symbol">}</a> <a id="22106" class="Symbol">→</a>
    <a id="22112" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22103" class="Bound">Γ</a> <a id="22114" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21806" class="Datatype Operator">⊢</a> <a id="22116" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3749" class="InductiveConstructor">false</a> <a id="22122" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21806" class="Datatype Operator">∶</a> <a id="22124" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a>
  <a id="_⊢_∶_.𝔹-E"></a><a id="22128" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22128" class="InductiveConstructor">𝔹-E</a> <a id="22132" class="Symbol">:</a> <a id="22134" class="Symbol">∀</a> <a id="22136" class="Symbol">{</a><a id="22137" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22137" class="Bound">Γ</a> <a id="22139" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22139" class="Bound">L</a> <a id="22141" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22141" class="Bound">M</a> <a id="22143" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22143" class="Bound">N</a> <a id="22145" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22145" class="Bound">A</a><a id="22146" class="Symbol">}</a> <a id="22148" class="Symbol">→</a>
    <a id="22154" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22137" class="Bound">Γ</a> <a id="22156" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21806" class="Datatype Operator">⊢</a> <a id="22158" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22139" class="Bound">L</a> <a id="22160" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21806" class="Datatype Operator">∶</a> <a id="22162" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="22164" class="Symbol">→</a>
    <a id="22170" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22137" class="Bound">Γ</a> <a id="22172" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21806" class="Datatype Operator">⊢</a> <a id="22174" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22141" class="Bound">M</a> <a id="22176" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21806" class="Datatype Operator">∶</a> <a id="22178" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22145" class="Bound">A</a> <a id="22180" class="Symbol">→</a>
    <a id="22186" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22137" class="Bound">Γ</a> <a id="22188" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21806" class="Datatype Operator">⊢</a> <a id="22190" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22143" class="Bound">N</a> <a id="22192" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21806" class="Datatype Operator">∶</a> <a id="22194" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22145" class="Bound">A</a> <a id="22196" class="Symbol">→</a>
    <a id="22202" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22137" class="Bound">Γ</a> <a id="22204" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21806" class="Datatype Operator">⊢</a> <a id="22206" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">if</a> <a id="22209" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22139" class="Bound">L</a> <a id="22211" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">then</a> <a id="22216" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22141" class="Bound">M</a> <a id="22218" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3764" class="InductiveConstructor Operator">else</a> <a id="22223" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22143" class="Bound">N</a> <a id="22225" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21806" class="Datatype Operator">∶</a> <a id="22227" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22145" class="Bound">A</a>{% endraw %}</pre>

#### Example type derivations

Here are a couple of typing examples.  First, here is how
they would be written in an informal description of the
formal semantics.

Derivation of `not`:

    ------------ Ax    ------------- 𝔹-I₂    ------------- 𝔹-I₁
    Γ₀ ⊢ ` x ∶ 𝔹       Γ₀ ⊢ false ∶ 𝔹         Γ₀ ⊢ true ∶ 𝔹
    ------------------------------------------------------ 𝔹-E
    Γ₀ ⊢ if ` x then false else true ∶ 𝔹
    --------------------------------------------------- ⇒-I
    ∅ ⊢ λ[ x ∶ 𝔹 ] if ` x then false else true ∶ 𝔹 ⇒ 𝔹

where `Γ₀ = ∅ , x ∶ 𝔹`.

Derivation of `two`:

                            ----------------- Ax     ------------ Ax
                            Γ₂ ⊢ ` f ∶ 𝔹 ⇒ 𝔹         Γ₂ ⊢ ` x ∶ 𝔹
    ----------------- Ax    ------------------------------------- ⇒-E
    Γ₂ ⊢ ` f ∶ 𝔹 ⇒ 𝔹        Γ₂ ⊢ ` f · ` x ∶ 𝔹
    -------------------------------------------  ⇒-E
    Γ₂ ⊢ ` f · (` f · ` x) ∶ 𝔹
    ------------------------------------------ ⇒-I
    Γ₁ ⊢ λ[ x ∶ 𝔹 ] ` f · (` f · ` x) ∶ 𝔹 ⇒ 𝔹
    ---------------------------------------------------------- ⇒-I
    ∅ ⊢ λ[ f ∶ 𝔹 ⇒ 𝔹 ] λ[ x ∶ 𝔹 ] ` f · (` f · ` x) ∶ 𝔹 ⇒ 𝔹

where `Γ₁ = ∅ , f ∶ 𝔹 ⇒ 𝔹` and `Γ₂ = ∅ , f ∶ 𝔹 ⇒ 𝔹 , x ∶ 𝔹`.

Here are the above derivations formalised in Agda.

<pre class="Agda">{% raw %}<a id="typing₁"></a><a id="23510" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#23510" class="Function">typing₁</a> <a id="23518" class="Symbol">:</a> <a id="23520" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#10265" class="Function">∅</a> <a id="23522" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21806" class="Datatype Operator">⊢</a> <a id="23524" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5720" class="Function">not</a> <a id="23528" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21806" class="Datatype Operator">∶</a> <a id="23530" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="23532" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2583" class="InductiveConstructor Operator">⇒</a> <a id="23534" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a>
<a id="23536" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#23510" class="Function">typing₁</a> <a id="23544" class="Symbol">=</a> <a id="23546" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21904" class="InductiveConstructor">⇒-I</a> <a id="23550" class="Symbol">(</a><a id="23551" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22128" class="InductiveConstructor">𝔹-E</a> <a id="23555" class="Symbol">(</a><a id="23556" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21850" class="InductiveConstructor">Ax</a> <a id="23559" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="23563" class="Symbol">)</a> <a id="23565" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22093" class="InductiveConstructor">𝔹-I₂</a> <a id="23570" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#22059" class="InductiveConstructor">𝔹-I₁</a><a id="23574" class="Symbol">)</a>

<a id="typing₂"></a><a id="23577" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#23577" class="Function">typing₂</a> <a id="23585" class="Symbol">:</a> <a id="23587" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#10265" class="Function">∅</a> <a id="23589" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21806" class="Datatype Operator">⊢</a> <a id="23591" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5724" class="Function">two</a> <a id="23595" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21806" class="Datatype Operator">∶</a> <a id="23597" class="Symbol">(</a><a id="23598" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="23600" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2583" class="InductiveConstructor Operator">⇒</a> <a id="23602" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a><a id="23603" class="Symbol">)</a> <a id="23605" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2583" class="InductiveConstructor Operator">⇒</a> <a id="23607" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="23609" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2583" class="InductiveConstructor Operator">⇒</a> <a id="23611" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a>
<a id="23613" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#23577" class="Function">typing₂</a> <a id="23621" class="Symbol">=</a> <a id="23623" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21904" class="InductiveConstructor">⇒-I</a> <a id="23627" class="Symbol">(</a><a id="23628" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21904" class="InductiveConstructor">⇒-I</a> <a id="23632" class="Symbol">(</a><a id="23633" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21981" class="InductiveConstructor">⇒-E</a> <a id="23637" class="Symbol">(</a><a id="23638" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21850" class="InductiveConstructor">Ax</a> <a id="23641" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="23645" class="Symbol">)</a> <a id="23647" class="Symbol">(</a><a id="23648" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21981" class="InductiveConstructor">⇒-E</a> <a id="23652" class="Symbol">(</a><a id="23653" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21850" class="InductiveConstructor">Ax</a> <a id="23656" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="23660" class="Symbol">)</a> <a id="23662" class="Symbol">(</a><a id="23663" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21850" class="InductiveConstructor">Ax</a> <a id="23666" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="23670" class="Symbol">))))</a>{% endraw %}</pre>

#### Interaction with Agda

Construction of a type derivation is best done interactively.
Start with the declaration:

    typing₁ : ∅ ⊢ not ∶ 𝔹 ⇒ 𝔹
    typing₁ = ?

Typing C-l causes Agda to create a hole and tell us its expected type.

    typing₁ = { }0
    ?0 : ∅ ⊢ not ∶ 𝔹 ⇒ 𝔹

Now we fill in the hole by typing C-c C-r. Agda observes that
the outermost term in `not` in a `λ`, which is typed using `⇒-I`. The
`⇒-I` rule in turn takes one argument, which Agda leaves as a hole.

    typing₁ = ⇒-I { }0
    ?0 : ∅ , x ∶ 𝔹 ⊢ if ` x then false else true ∶ 𝔹

Again we fill in the hole by typing C-c C-r. Agda observes that the
outermost term is now `if_then_else_`, which is typed using `𝔹-E`. The
`𝔹-E` rule in turn takes three arguments, which Agda leaves as holes.

    typing₁ = ⇒-I (𝔹-E { }0 { }1 { }2)
    ?0 : ∅ , x ∶ 𝔹 ⊢ ` x ∶
    ?1 : ∅ , x ∶ 𝔹 ⊢ false ∶ 𝔹
    ?2 : ∅ , x ∶ 𝔹 ⊢ true ∶ 𝔹

Again we fill in the three holes by typing C-c C-r in each. Agda observes
that `` ` x ``, `false`, and `true` are typed using `Ax`, `𝔹-I₂`, and
`𝔹-I₁` respectively. The `Ax` rule in turn takes an argument, to show
that `(∅ , x ∶ 𝔹) x = just 𝔹`, which can in turn be specified with a
hole. After filling in all holes, the term is as above.

The entire process can be automated using Agsy, invoked with C-c C-a.

#### Non-examples

We can also show that terms are _not_ typeable.  For example, here is
a formal proof that it is not possible to type the term `` true ·
false ``.  In other words, no type `A` is the type of this term.  It
cannot be typed, because doing so requires that the first term in the
application is both a boolean and a function.

<pre class="Agda">{% raw %}<a id="notyping₂"></a><a id="25351" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#25351" class="Function">notyping₂</a> <a id="25361" class="Symbol">:</a> <a id="25363" class="Symbol">∀</a> <a id="25365" class="Symbol">{</a><a id="25366" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#25366" class="Bound">A</a><a id="25367" class="Symbol">}</a> <a id="25369" class="Symbol">→</a> <a id="25371" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#464" class="Function Operator">¬</a> <a id="25373" class="Symbol">(</a><a id="25374" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#10265" class="Function">∅</a> <a id="25376" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21806" class="Datatype Operator">⊢</a> <a id="25378" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3735" class="InductiveConstructor">true</a> <a id="25383" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="25385" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3749" class="InductiveConstructor">false</a> <a id="25391" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21806" class="Datatype Operator">∶</a> <a id="25393" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#25366" class="Bound">A</a><a id="25394" class="Symbol">)</a>
<a id="25396" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#25351" class="Function">notyping₂</a> <a id="25406" class="Symbol">(</a><a id="25407" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21981" class="InductiveConstructor">⇒-E</a> <a id="25411" class="Symbol">()</a> <a id="25414" class="Symbol">_)</a>{% endraw %}</pre>

As a second example, here is a formal proof that it is not possible to
type `` λ[ x ∶ 𝔹 ] λ[ y ∶ 𝔹 ] ` x · ` y `` It cannot be typed, because
doing so requires `x` to be both boolean and a function.

<pre class="Agda">{% raw %}<a id="contradiction"></a><a id="25642" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#25642" class="Function">contradiction</a> <a id="25656" class="Symbol">:</a> <a id="25658" class="Symbol">∀</a> <a id="25660" class="Symbol">{</a><a id="25661" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#25661" class="Bound">A</a> <a id="25663" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#25663" class="Bound">B</a><a id="25664" class="Symbol">}</a> <a id="25666" class="Symbol">→</a> <a id="25668" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#464" class="Function Operator">¬</a> <a id="25670" class="Symbol">(</a><a id="25671" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="25673" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="25675" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#25661" class="Bound">A</a> <a id="25677" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2583" class="InductiveConstructor Operator">⇒</a> <a id="25679" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#25663" class="Bound">B</a><a id="25680" class="Symbol">)</a>
<a id="25682" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#25642" class="Function">contradiction</a> <a id="25696" class="Symbol">()</a>

<a id="notyping₁"></a><a id="25700" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#25700" class="Function">notyping₁</a> <a id="25710" class="Symbol">:</a> <a id="25712" class="Symbol">∀</a> <a id="25714" class="Symbol">{</a><a id="25715" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#25715" class="Bound">A</a><a id="25716" class="Symbol">}</a> <a id="25718" class="Symbol">→</a> <a id="25720" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#464" class="Function Operator">¬</a> <a id="25722" class="Symbol">(</a><a id="25723" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#10265" class="Function">∅</a> <a id="25725" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21806" class="Datatype Operator">⊢</a> <a id="25727" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[</a> <a id="25730" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">x</a> <a id="25732" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">∶</a> <a id="25734" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="25736" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">]</a> <a id="25738" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">λ[</a> <a id="25741" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5679" class="Function">y</a> <a id="25743" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">∶</a> <a id="25745" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#2610" class="InductiveConstructor">𝔹</a> <a id="25747" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3672" class="InductiveConstructor Operator">]</a> <a id="25749" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="25751" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5677" class="Function">x</a> <a id="25753" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3708" class="InductiveConstructor Operator">·</a> <a id="25755" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#3656" class="InductiveConstructor">`</a> <a id="25757" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#5679" class="Function">y</a> <a id="25759" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21806" class="Datatype Operator">∶</a> <a id="25761" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#25715" class="Bound">A</a><a id="25762" class="Symbol">)</a>
<a id="25764" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#25700" class="Function">notyping₁</a> <a id="25774" class="Symbol">(</a><a id="25775" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21904" class="InductiveConstructor">⇒-I</a> <a id="25779" class="Symbol">(</a><a id="25780" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21904" class="InductiveConstructor">⇒-I</a> <a id="25784" class="Symbol">(</a><a id="25785" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21981" class="InductiveConstructor">⇒-E</a> <a id="25789" class="Symbol">(</a><a id="25790" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#21850" class="InductiveConstructor">Ax</a> <a id="25793" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#25793" class="Bound">Γx</a><a id="25795" class="Symbol">)</a> <a id="25797" class="Symbol">_)))</a> <a id="25802" class="Symbol">=</a>  <a id="25805" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#25642" class="Function">contradiction</a> <a id="25819" class="Symbol">(</a><a id="25820" href="{% endraw %}{{ site.baseurl }}{% link out/Maps.md %}{% raw %}#11919" class="Function">just-injective</a> <a id="25835" href="{% endraw %}{{ site.baseurl }}{% link out/Stlc.md %}{% raw %}#25793" class="Bound">Γx</a><a id="25837" class="Symbol">)</a>{% endraw %}</pre>


#### Quiz

For each of the following, given a type `A` for which it is derivable,
or explain why there is no such `A`.

1. `` ∅ , y ∶ A ⊢ λ[ x ∶ 𝔹 ] ` x ∶ 𝔹 ⇒ 𝔹 ``
2. `` ∅ ⊢ λ[ y ∶ 𝔹 ⇒ 𝔹 ] λ[ x ∶ 𝔹 ] ` y · ` x ∶ A ``
3. `` ∅ ⊢ λ[ y ∶ 𝔹 ⇒ 𝔹 ] λ[ x ∶ 𝔹 ] ` x · ` y ∶ A ``
4. `` ∅ , x ∶ A ⊢ λ[ y : 𝔹 ⇒ 𝔹 ] `y · `x : A ``

For each of the following, give type `A`, `B`, `C`, and `D` for which it is derivable,
or explain why there are no such types.

1. `` ∅ ⊢ λ[ y ∶ 𝔹 ⇒ 𝔹 ⇒ 𝔹 ] λ[ x ∶ 𝔹 ] ` y · ` x ∶ A ``
2. `` ∅ , x ∶ A ⊢ x · x ∶ B ``
3. `` ∅ , x ∶ A , y ∶ B ⊢ λ[ z ∶ C ] ` x · (` y · ` z) ∶ D ``



