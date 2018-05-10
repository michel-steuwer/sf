---
title     : "Properties: Proof by Induction"
layout    : page
permalink : /Properties
---

Now that we've defined the naturals and operations upon them, our next
step is to learn how to prove properties that they satisfy.  As hinted
by their name, properties of *inductive datatypes* are proved by
*induction*.


## Imports

We require equivalence as in the previous chapter, plus the naturals
and some operations upon them.  We also import a couple of new operations,
`cong`, `sym`, and `_≡⟨_⟩_`, which are explained below.
<pre class="Agda">{% raw %}<a id="543" class="Keyword">import</a> <a id="550" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="588" class="Symbol">as</a> <a id="591" class="Module">Eq</a>
<a id="594" class="Keyword">open</a> <a id="599" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="602" class="Keyword">using</a> <a id="608" class="Symbol">(</a><a id="609" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">_≡_</a><a id="612" class="Symbol">;</a> <a id="614" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="618" class="Symbol">;</a> <a id="620" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#981" class="Function">cong</a><a id="624" class="Symbol">;</a> <a id="626" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#565" class="Function">sym</a><a id="629" class="Symbol">)</a>
<a id="631" class="Keyword">open</a> <a id="636" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3767" class="Module">Eq.≡-Reasoning</a> <a id="651" class="Keyword">using</a> <a id="657" class="Symbol">(</a><a id="658" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3868" class="Function Operator">begin_</a><a id="664" class="Symbol">;</a> <a id="666" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3926" class="Function Operator">_≡⟨⟩_</a><a id="671" class="Symbol">;</a> <a id="673" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3985" class="Function Operator">_≡⟨_⟩_</a><a id="679" class="Symbol">;</a> <a id="681" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4166" class="Function Operator">_∎</a><a id="683" class="Symbol">)</a>
<a id="685" class="Keyword">open</a> <a id="690" class="Keyword">import</a> <a id="697" href="https://agda.github.io/agda-stdlib/Data.Nat.html" class="Module">Data.Nat</a> <a id="706" class="Keyword">using</a> <a id="712" class="Symbol">(</a><a id="713" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="714" class="Symbol">;</a> <a id="716" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="720" class="Symbol">;</a> <a id="722" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a><a id="725" class="Symbol">;</a> <a id="727" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">_+_</a><a id="730" class="Symbol">;</a> <a id="732" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#433" class="Primitive Operator">_*_</a><a id="735" class="Symbol">;</a> <a id="737" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#320" class="Primitive Operator">_∸_</a><a id="740" class="Symbol">)</a>{% endraw %}</pre>


## Associativity

One property of addition is that it is *associative*, that is, that the
order of the parentheses does not matter:

    (m + n) + p ≡ m + (n + p)

Here `m`, `n`, and `p` are variables that range over all natural numbers.

We can test the proposition by choosing specific numbers for the three
variables.
<pre class="Agda">{% raw %}<a id="1089" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#1089" class="Function">_</a> <a id="1091" class="Symbol">:</a> <a id="1093" class="Symbol">(</a><a id="1094" class="Number">3</a> <a id="1096" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="1098" class="Number">4</a><a id="1099" class="Symbol">)</a> <a id="1101" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="1103" class="Number">5</a> <a id="1105" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="1107" class="Number">3</a> <a id="1109" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="1111" class="Symbol">(</a><a id="1112" class="Number">4</a> <a id="1114" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="1116" class="Number">5</a><a id="1117" class="Symbol">)</a>
<a id="1119" class="Symbol">_</a> <a id="1121" class="Symbol">=</a>
  <a id="1125" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3868" class="Function Operator">begin</a>
    <a id="1135" class="Symbol">(</a><a id="1136" class="Number">3</a> <a id="1138" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="1140" class="Number">4</a><a id="1141" class="Symbol">)</a> <a id="1143" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="1145" class="Number">5</a>
  <a id="1149" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3926" class="Function Operator">≡⟨⟩</a>
    <a id="1157" class="Number">7</a> <a id="1159" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="1161" class="Number">5</a>
  <a id="1165" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3926" class="Function Operator">≡⟨⟩</a>
    <a id="1173" class="Number">12</a>
  <a id="1178" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3926" class="Function Operator">≡⟨⟩</a>
    <a id="1186" class="Number">3</a> <a id="1188" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="1190" class="Number">9</a>
  <a id="1194" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3926" class="Function Operator">≡⟨⟩</a>
    <a id="1202" class="Number">3</a> <a id="1204" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="1206" class="Symbol">(</a><a id="1207" class="Number">4</a> <a id="1209" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="1211" class="Number">5</a><a id="1212" class="Symbol">)</a>
  <a id="1216" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4166" class="Function Operator">∎</a>{% endraw %}</pre>
Here we have displayed the computation as a chain of equations,
one term to a line.  It is often easiest to read such chains from the top down
until one reaches the simplest term (in this case, `12`), and
then from the bottom up until one reaches the same term.

The test reveals that associativity is perhaps not as obvious as first
it appears.  Why should `7 + 5` be the same as `3 + 9`?  We might want
to gather more evidence, testing the proposition by choosing other
numbers.  But---since there are an infinite number of
naturals---testing can never be complete.  Is there any way we can be
sure that associativity holds for *all* the natural numbers?

The answer is yes! We can prove a property holds for all naturals using
*proof by induction*.


## Proof by induction

Recall the definition of natural numbers consists of a *base case*
which tells us that `zero` is a natural, and an *inductive case*
which tells us that if `m` is a natural then `suc m` is also a natural.

Proof by induction follows the structure of this definition.  To prove
a property of natural numbers by induction, we need prove two cases.
First is the *base case*, where we show the property holds for `zero`.
Second is the *inductive case*, where we assume the the property holds for
an arbitrary natural `m` (we call this the *inductive hypothesis*), and
then show that the property must also hold for `suc m`.

If we write `P m` for a property of `m`, then what we need to
demonstrate are the following two inference rules:

    ------
    P zero

    P m
    ---------
    P (suc m)

Let's unpack these rules.  The first rule is the base case, and
requires we show that property `P` holds for `zero`.  The second rule
is the inductive case, and requires we show that if we assume the
inductive hypothesis, namely that `P` holds for `m`, then it follows that
`P` also holds for `suc m`.

Why does this work?  Again, it can be explained by a creation story.
To start with, we know no properties.

    -- in the beginning, no properties are known

Now, we apply the two rules to all the properties we know about.  The
base case tells us that `P zero` holds, so we add it to the set of
known properties.  The inductive case tells us that if `P m` holds (on
the day before today) then `P (suc m)` also holds (today).  We didn't
know about any properties before today, so the inductive case doesn't
apply.

    -- on the first day, one property is known
    P zero

Then we repeat the process, so on the next day we know about all the
properties from the day before, plus any properties added by the rules.
The base case tells us that `P zero` holds, but we already
knew that. But now the inductive case tells us that since `P zero`
held yesterday, then `P (suc zero)` holds today.

    -- on the second day, two properties are known
    P zero
    P (suc zero)

And we repeat the process again. Now the inductive case
tells us that since `P zero` and `P (suc zero)` both hold, then
`P (suc zero)` and `P (suc (suc zero))` also hold. We already knew about
the first of these, but the second is new.

    -- on the third day, three properties are known
    P zero
    P (suc zero)
    P (suc (suc zero))

You've probably got the hang of it by now.

    -- on the fourth day, four properties are known
    P zero
    P (suc zero)
    P (suc (suc zero))
    P (suc (suc (suc zero)))

The process continues.  On the *n*th day there will be *n* distinct
properties that hold.  The property of every natural number will appear
on some given day.  In particular, the property `P n` first appears on
day *n+1*. 


## Our first proof: associativity

In order to prove associativity, we take `P m` to be the property

    (m + n) + p ≡ m + (n + p)

Here `n` and `p` are arbitrary natural numbers, so if we can show the
equation holds for all `m` it will also hold for all `n` and `p`.
The appropriate instances of the inference rules are:

    -------------------------------
    (zero + n) + p ≡ zero + (n + p)

    (m + n) + p ≡ m + (n + p)
    ---------------------------------
    (suc m + n) + p ≡ (suc m + n) + p

If we can demonstrate both of these, then associativity of addition
follows by induction.

Here is the proposition's statement and proof.
<pre class="Agda">{% raw %}<a id="+-assoc"></a><a id="5471" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#5471" class="Function">+-assoc</a> <a id="5479" class="Symbol">:</a> <a id="5481" class="Symbol">∀</a> <a id="5483" class="Symbol">(</a><a id="5484" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#5484" class="Bound">m</a> <a id="5486" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#5486" class="Bound">n</a> <a id="5488" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#5488" class="Bound">p</a> <a id="5490" class="Symbol">:</a> <a id="5492" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="5493" class="Symbol">)</a> <a id="5495" class="Symbol">→</a> <a id="5497" class="Symbol">(</a><a id="5498" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#5484" class="Bound">m</a> <a id="5500" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5502" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#5486" class="Bound">n</a><a id="5503" class="Symbol">)</a> <a id="5505" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5507" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#5488" class="Bound">p</a> <a id="5509" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="5511" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#5484" class="Bound">m</a> <a id="5513" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5515" class="Symbol">(</a><a id="5516" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#5486" class="Bound">n</a> <a id="5518" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5520" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#5488" class="Bound">p</a><a id="5521" class="Symbol">)</a>
<a id="5523" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#5471" class="Function">+-assoc</a> <a id="5531" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="5536" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#5536" class="Bound">n</a> <a id="5538" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#5538" class="Bound">p</a> <a id="5540" class="Symbol">=</a>
  <a id="5544" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3868" class="Function Operator">begin</a>
    <a id="5554" class="Symbol">(</a><a id="5555" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="5560" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5562" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#5536" class="Bound">n</a><a id="5563" class="Symbol">)</a> <a id="5565" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5567" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#5538" class="Bound">p</a>
  <a id="5571" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3926" class="Function Operator">≡⟨⟩</a>
    <a id="5579" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#5536" class="Bound">n</a> <a id="5581" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5583" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#5538" class="Bound">p</a>
  <a id="5587" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3926" class="Function Operator">≡⟨⟩</a>
   <a id="5594" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="5599" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5601" class="Symbol">(</a><a id="5602" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#5536" class="Bound">n</a> <a id="5604" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5606" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#5538" class="Bound">p</a><a id="5607" class="Symbol">)</a>
  <a id="5611" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4166" class="Function Operator">∎</a>
<a id="5613" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#5471" class="Function">+-assoc</a> <a id="5621" class="Symbol">(</a><a id="5622" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="5626" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#5626" class="Bound">m</a><a id="5627" class="Symbol">)</a> <a id="5629" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#5629" class="Bound">n</a> <a id="5631" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#5631" class="Bound">p</a> <a id="5633" class="Symbol">=</a>
  <a id="5637" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3868" class="Function Operator">begin</a>
    <a id="5647" class="Symbol">(</a><a id="5648" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="5652" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#5626" class="Bound">m</a> <a id="5654" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5656" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#5629" class="Bound">n</a><a id="5657" class="Symbol">)</a> <a id="5659" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5661" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#5631" class="Bound">p</a>
  <a id="5665" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3926" class="Function Operator">≡⟨⟩</a>
    <a id="5673" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="5677" class="Symbol">(</a><a id="5678" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#5626" class="Bound">m</a> <a id="5680" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5682" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#5629" class="Bound">n</a><a id="5683" class="Symbol">)</a> <a id="5685" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5687" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#5631" class="Bound">p</a>
  <a id="5691" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3926" class="Function Operator">≡⟨⟩</a>
    <a id="5699" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="5703" class="Symbol">((</a><a id="5705" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#5626" class="Bound">m</a> <a id="5707" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5709" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#5629" class="Bound">n</a><a id="5710" class="Symbol">)</a> <a id="5712" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5714" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#5631" class="Bound">p</a><a id="5715" class="Symbol">)</a>
  <a id="5719" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3985" class="Function Operator">≡⟨</a> <a id="5722" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#981" class="Function">cong</a> <a id="5727" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="5731" class="Symbol">(</a><a id="5732" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#5471" class="Function">+-assoc</a> <a id="5740" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#5626" class="Bound">m</a> <a id="5742" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#5629" class="Bound">n</a> <a id="5744" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#5631" class="Bound">p</a><a id="5745" class="Symbol">)</a> <a id="5747" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3985" class="Function Operator">⟩</a>
    <a id="5753" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="5757" class="Symbol">(</a><a id="5758" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#5626" class="Bound">m</a> <a id="5760" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5762" class="Symbol">(</a><a id="5763" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#5629" class="Bound">n</a> <a id="5765" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5767" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#5631" class="Bound">p</a><a id="5768" class="Symbol">))</a>
  <a id="5773" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3926" class="Function Operator">≡⟨⟩</a>
    <a id="5781" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="5785" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#5626" class="Bound">m</a> <a id="5787" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5789" class="Symbol">(</a><a id="5790" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#5629" class="Bound">n</a> <a id="5792" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="5794" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#5631" class="Bound">p</a><a id="5795" class="Symbol">)</a>
  <a id="5799" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4166" class="Function Operator">∎</a>{% endraw %}</pre>
We have named the proof `+-assoc`.  In Agda, identifiers can consist of
any sequence of characters not including spaces or the characters `@.(){};_`.

Let's unpack this code.  The signature states that we are
defining the identifier `+-assoc` which provide evidence for the
proposition:

    ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)

The upside down A is pronounced "for all", and the proposition
asserts that for all natural numbers `m`, `n`, and `p` that
the equation `(m + n) + p ≡ m + (n + p)` holds.  Evidence for the proposition
is a function that accepts three natural numbers, binds them to `m`, `n`, and `p`,
and returns evidence for the corresponding instance of the equation.

For the base case, we must show:

    (zero + n) + p ≡ zero + (n + p)

Simplifying both sides with the base case of addition yields the equation:

   n + p ≡ n + p

This holds trivially.  Reading the chain of equations in the base case of the proof,
the top and bottom of the chain match the two sides of the equation to
be shown, and reading down from the top and up from the bottom takes us to
`n + p` in the middle.  No justification other than simplification is required.

For the inductive case, we must show:

    (suc m + n) + p ≡ suc m + (n + p)

Simplifying both sides with the inductive case of addition yields the equation:

   suc ((m + n) + p) ≡ suc (m + (n + p))

This in turn follows by prefacing `suc` to both sides of the induction
hypothesis:

    (m + n) + p ≡ m + (n + p)

Reading the chain of equations in the inductive case of the proof, the
top and bottom of the chain match the two sides of the equation to be
shown, and reading down from the top and up from the bottom takes us
to the simplified equation above. The remaining equation, does not follow
from simplification alone, so we use an additional operator for chain
reasoning, `_≡⟨_⟩_`, where a justification for the equation appears
within angle brackets.  The justification given is:

    ⟨ cong suc (+-assoc m n p) ⟩

Here, the recursive invocation `+-assoc m n p` has as its type the
induction hypothesis, and `cong suc` prefaces `suc` to each side to
yield the needed equation.

A relation is said to be a *congruence* for a given function if it is
preserved by applying that function.  If `e` is evidence that `x ≡ y`,
then `cong f e` is evidence that `f x ≡ f y`, for any function `f`.

Here the inductive hypothesis is not assumed, but instead proved by a
recursive invocation of the function we are defining, `+-assoc m n p`.
As with addition, this is well founded because associativity of
larger numbers is proved in terms of associativity of smaller numbers.
In this case, `assoc (suc m) n p` is proved using `assoc m n p`.
The correspondence between proof by induction and definition by
recursion is one of the most appealing aspects of Agda.


## Our second proof: commutativity

Another important property of addition is that it is *commutative*, that is,
that the order of the operands does not matter:

    m + n ≡ n + m

The proof requires that we first demonstrate two lemmas.

### The first lemma

The base case of the definition of addition states that zero
is a left-identity:

    zero + n ≡ n

Our first lemma states that zero is also a right-identity:

    m + zero ≡ m

Here is the lemma's statement and proof.
<pre class="Agda">{% raw %}<a id="+-identityʳ"></a><a id="9133" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#9133" class="Function">+-identityʳ</a> <a id="9145" class="Symbol">:</a> <a id="9147" class="Symbol">∀</a> <a id="9149" class="Symbol">(</a><a id="9150" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#9150" class="Bound">m</a> <a id="9152" class="Symbol">:</a> <a id="9154" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="9155" class="Symbol">)</a> <a id="9157" class="Symbol">→</a> <a id="9159" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#9150" class="Bound">m</a> <a id="9161" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="9163" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="9168" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="9170" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#9150" class="Bound">m</a>
<a id="9172" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#9133" class="Function">+-identityʳ</a> <a id="9184" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="9189" class="Symbol">=</a>
  <a id="9193" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3868" class="Function Operator">begin</a>
    <a id="9203" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="9208" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="9210" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>
  <a id="9217" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3926" class="Function Operator">≡⟨⟩</a>
    <a id="9225" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>
  <a id="9232" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4166" class="Function Operator">∎</a>
<a id="9234" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#9133" class="Function">+-identityʳ</a> <a id="9246" class="Symbol">(</a><a id="9247" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="9251" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#9251" class="Bound">m</a><a id="9252" class="Symbol">)</a> <a id="9254" class="Symbol">=</a>
  <a id="9258" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3868" class="Function Operator">begin</a>
    <a id="9268" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="9272" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#9251" class="Bound">m</a> <a id="9274" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="9276" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>
  <a id="9283" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3926" class="Function Operator">≡⟨⟩</a>
    <a id="9291" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="9295" class="Symbol">(</a><a id="9296" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#9251" class="Bound">m</a> <a id="9298" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="9300" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="9304" class="Symbol">)</a>
  <a id="9308" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3985" class="Function Operator">≡⟨</a> <a id="9311" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#981" class="Function">cong</a> <a id="9316" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="9320" class="Symbol">(</a><a id="9321" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#9133" class="Function">+-identityʳ</a> <a id="9333" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#9251" class="Bound">m</a><a id="9334" class="Symbol">)</a> <a id="9336" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3985" class="Function Operator">⟩</a>
    <a id="9342" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="9346" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#9251" class="Bound">m</a>
  <a id="9350" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4166" class="Function Operator">∎</a>{% endraw %}</pre>
The signature states that we are defining the identifier `+-identityʳ` which
provides evidence for the proposition:

    ∀ (m : ℕ) → m + zero ≡ m

Evidence for the proposition is a function that accepts a natural
number, binds it to `m`, and returns evidence for the corresponding
instance of the equation.  The proof is by induction on `m`.

For the base case, we must show:

    zero + zero ≡ zero

Simplifying with the base case of of addition, this is straightforward.

For the inductive case, we must show:

    (suc m) + zero = suc m

Simplifying both sides with the inductive case of addition yields the equation:

    suc (m + zero) = suc m

This in turn follows by prefacing `suc` to both sides of the induction
hypothesis:

    m + zero ≡ m

Reading the chain of equations down from the top and up from the bottom
takes us to the simplified equation above.  The remaining
equation has the justification:

    ⟨ cong suc (+-identityʳ m) ⟩

Here, the recursive invocation `+-identityʳ m` has as its type the
induction hypothesis, and `cong suc` prefaces `suc` to each side to
yield the needed equation.  This completes the first lemma.

### The second lemma

The inductive case of the definition of addition pushes `suc` on the
first argument to the outside:

    suc m + n ≡ suc (m + n)

Our second lemma does the same for `suc` on the second argument:

    m + suc n ≡ suc (m + n)

Here is the lemma's statement and proof.
<pre class="Agda">{% raw %}<a id="+-suc"></a><a id="10809" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#10809" class="Function">+-suc</a> <a id="10815" class="Symbol">:</a> <a id="10817" class="Symbol">∀</a> <a id="10819" class="Symbol">(</a><a id="10820" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#10820" class="Bound">m</a> <a id="10822" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#10822" class="Bound">n</a> <a id="10824" class="Symbol">:</a> <a id="10826" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="10827" class="Symbol">)</a> <a id="10829" class="Symbol">→</a> <a id="10831" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#10820" class="Bound">m</a> <a id="10833" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="10835" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="10839" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#10822" class="Bound">n</a> <a id="10841" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="10843" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="10847" class="Symbol">(</a><a id="10848" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#10820" class="Bound">m</a> <a id="10850" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="10852" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#10822" class="Bound">n</a><a id="10853" class="Symbol">)</a>
<a id="10855" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#10809" class="Function">+-suc</a> <a id="10861" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="10866" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#10866" class="Bound">n</a> <a id="10868" class="Symbol">=</a>
  <a id="10872" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3868" class="Function Operator">begin</a>
    <a id="10882" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="10887" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="10889" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="10893" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#10866" class="Bound">n</a>
  <a id="10897" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3926" class="Function Operator">≡⟨⟩</a>
    <a id="10905" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="10909" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#10866" class="Bound">n</a>
  <a id="10913" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3926" class="Function Operator">≡⟨⟩</a>
    <a id="10921" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="10925" class="Symbol">(</a><a id="10926" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="10931" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="10933" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#10866" class="Bound">n</a><a id="10934" class="Symbol">)</a>
  <a id="10938" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4166" class="Function Operator">∎</a>
<a id="10940" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#10809" class="Function">+-suc</a> <a id="10946" class="Symbol">(</a><a id="10947" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="10951" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#10951" class="Bound">m</a><a id="10952" class="Symbol">)</a> <a id="10954" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#10954" class="Bound">n</a> <a id="10956" class="Symbol">=</a>
  <a id="10960" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3868" class="Function Operator">begin</a>
    <a id="10970" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="10974" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#10951" class="Bound">m</a> <a id="10976" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="10978" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="10982" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#10954" class="Bound">n</a>
  <a id="10986" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3926" class="Function Operator">≡⟨⟩</a>
    <a id="10994" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="10998" class="Symbol">(</a><a id="10999" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#10951" class="Bound">m</a> <a id="11001" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11003" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11007" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#10954" class="Bound">n</a><a id="11008" class="Symbol">)</a>
  <a id="11012" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3985" class="Function Operator">≡⟨</a> <a id="11015" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#981" class="Function">cong</a> <a id="11020" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11024" class="Symbol">(</a><a id="11025" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#10809" class="Function">+-suc</a> <a id="11031" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#10951" class="Bound">m</a> <a id="11033" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#10954" class="Bound">n</a><a id="11034" class="Symbol">)</a> <a id="11036" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3985" class="Function Operator">⟩</a>
    <a id="11042" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11046" class="Symbol">(</a><a id="11047" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11051" class="Symbol">(</a><a id="11052" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#10951" class="Bound">m</a> <a id="11054" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11056" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#10954" class="Bound">n</a><a id="11057" class="Symbol">))</a>
  <a id="11062" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3926" class="Function Operator">≡⟨⟩</a>
    <a id="11070" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11074" class="Symbol">(</a><a id="11075" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="11079" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#10951" class="Bound">m</a> <a id="11081" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="11083" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#10954" class="Bound">n</a><a id="11084" class="Symbol">)</a>
  <a id="11088" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4166" class="Function Operator">∎</a>{% endraw %}</pre>
The signature states that we are defining the identifier `+-suc` which provides
evidence for the proposition:

    ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

Evidence for the proposition is a function that accepts two natural numbers,
binds them to `m` and `n`, and returns evidence for the corresponding instance
of the equation.  The proof is by induction on `m`.

For the base case, we must show:

    zero + suc n ≡ suc (zero + n)

Simplifying with the base case of of addition, this is straightforward.

For the inductive case, we must show:

    suc m + suc n ≡ suc (suc m + n)

Simplifying both sides with the inductive case of addition yields the equation:

    suc (m + suc n) ≡ suc (suc (m + n))

This in turn follows by prefacing `suc` to both sides of the induction
hypothesis:

    m + suc n ≡ suc (m + n)

Reading the chain of equations down from the top and up from the bottom
takes us to the simplified equation in the middle.  The remaining
equation has the justification:

    ⟨ cong suc (+-suc m n) ⟩

Here, the recursive invocation `+-suc m n` has as its type the
induction hypothesis, and `cong suc` prefaces `suc` to each side to
yield the needed equation.  This completes the second lemma.

### The proposition

Finally, here is our proposition's statement and proof.
<pre class="Agda">{% raw %}<a id="+-comm"></a><a id="12401" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#12401" class="Function">+-comm</a> <a id="12408" class="Symbol">:</a> <a id="12410" class="Symbol">∀</a> <a id="12412" class="Symbol">(</a><a id="12413" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#12413" class="Bound">m</a> <a id="12415" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#12415" class="Bound">n</a> <a id="12417" class="Symbol">:</a> <a id="12419" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="12420" class="Symbol">)</a> <a id="12422" class="Symbol">→</a> <a id="12424" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#12413" class="Bound">m</a> <a id="12426" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="12428" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#12415" class="Bound">n</a> <a id="12430" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="12432" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#12415" class="Bound">n</a> <a id="12434" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="12436" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#12413" class="Bound">m</a>
<a id="12438" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#12401" class="Function">+-comm</a> <a id="12445" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#12445" class="Bound">m</a> <a id="12447" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="12452" class="Symbol">=</a>
  <a id="12456" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3868" class="Function Operator">begin</a>
    <a id="12466" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#12445" class="Bound">m</a> <a id="12468" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="12470" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>
  <a id="12477" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3985" class="Function Operator">≡⟨</a> <a id="12480" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#9133" class="Function">+-identityʳ</a> <a id="12492" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#12445" class="Bound">m</a> <a id="12494" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3985" class="Function Operator">⟩</a>
    <a id="12500" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#12445" class="Bound">m</a>
  <a id="12504" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3926" class="Function Operator">≡⟨⟩</a>
    <a id="12512" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="12517" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="12519" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#12445" class="Bound">m</a>
  <a id="12523" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4166" class="Function Operator">∎</a>
<a id="12525" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#12401" class="Function">+-comm</a> <a id="12532" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#12532" class="Bound">m</a> <a id="12534" class="Symbol">(</a><a id="12535" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12539" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#12539" class="Bound">n</a><a id="12540" class="Symbol">)</a> <a id="12542" class="Symbol">=</a>
  <a id="12546" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3868" class="Function Operator">begin</a>
    <a id="12556" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#12532" class="Bound">m</a> <a id="12558" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="12560" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12564" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#12539" class="Bound">n</a>
  <a id="12568" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3985" class="Function Operator">≡⟨</a> <a id="12571" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#10809" class="Function">+-suc</a> <a id="12577" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#12532" class="Bound">m</a> <a id="12579" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#12539" class="Bound">n</a> <a id="12581" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3985" class="Function Operator">⟩</a>
    <a id="12587" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12591" class="Symbol">(</a><a id="12592" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#12532" class="Bound">m</a> <a id="12594" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="12596" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#12539" class="Bound">n</a><a id="12597" class="Symbol">)</a>
  <a id="12601" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3985" class="Function Operator">≡⟨</a> <a id="12604" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#981" class="Function">cong</a> <a id="12609" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12613" class="Symbol">(</a><a id="12614" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#12401" class="Function">+-comm</a> <a id="12621" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#12532" class="Bound">m</a> <a id="12623" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#12539" class="Bound">n</a><a id="12624" class="Symbol">)</a> <a id="12626" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3985" class="Function Operator">⟩</a>
    <a id="12632" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12636" class="Symbol">(</a><a id="12637" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#12539" class="Bound">n</a> <a id="12639" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="12641" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#12532" class="Bound">m</a><a id="12642" class="Symbol">)</a>
  <a id="12646" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#3926" class="Function Operator">≡⟨⟩</a>
    <a id="12654" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="12658" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#12539" class="Bound">n</a> <a id="12660" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="12662" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#12532" class="Bound">m</a>
  <a id="12666" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html#4166" class="Function Operator">∎</a>{% endraw %}</pre>
The first line states that we are defining the identifier
`+-comm` which provides evidence for the proposition:

    ∀ (m n : ℕ) → m + n ≡ n + m

Evidence for the proposition is a function that accepts two
natural numbers, binds them to `m` and `n`, and returns evidence for the
corresponding instance of the equation.  The proof is by
induction on `n`.  (Not on `m` this time!)

For the base case, we must show:

    m + zero ≡ zero + m

Simplifying both sides with the base case of addition yields the equation:

    m + zero ≡ m

The the remaining equation has the justification

    ⟨ +-identityʳ m ⟩

which invokes the first lemma.

For the inductive case, we must show:

    m + suc n ≡ suc n + m

Simplifying both sides with the inductive case of addition yields the equation:

    m + suc n ≡ suc (n + m)

We show this in two steps.  First, we have:

    m + suc n ≡ suc (m + n)

which is justified by the second lemma, `⟨ +-suc m n ⟩`.  Then we
have

    suc (m + n) ≡ suc (n + m)

which is justified by congruence and the induction hypothesis,
`⟨ cong suc (+-comm m n) ⟩`.  This completes the proposition.

Agda requires that identifiers are defined before they are used,
so we must present the lemmas before the main proposition, as we
have done above.  In practice, one will often attempt to prove
the main proposition first, and the equations required to do so
will suggest what lemmas to prove.



## Creation, one last time

Returning to the proof of associativity, it may be helpful to view the inductive
proof (or, equivalently, the recursive definition) as a creation story.  This
time we are concerned with judgements asserting associativity.

     -- in the beginning, we know nothing about associativity

Now, we apply the rules to all the judgements we know about.  The base
case tells us that `(zero + n) + p ≡ zero + (n + p)` for every natural
`n` and `p`.  The inductive case tells us that if `(m + n) + p ≡ m +
(n + p)` (on the day before today) then `(suc m + n) + p ≡ suc m + (n
+ p)` (today).  We didn't know any judgments about associativity
before today, so that rule doesn't give us any new judgments.

    -- on the first day, we know about associativity of 0
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    
Then we repeat the process, so on the next day we know about all the
judgements from the day before, plus any judgements added by the rules.
The base case tells us nothing new, but now the inductive case adds
more judgements.

    -- on the second day, we know about associativity of 0 and 1
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...

And we repeat the process again.

    -- on the third day, we know about associativity of 0, 1, and 2
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...
    (2 + 0) + 0 ≡ 2 + (0 + 0)   ...   (2 + 4) + 5 ≡ 2 + (4 + 5)   ...

You've got the hang of it by now.

    -- on the fourth day, we know about associativity of 0, 1, 2, and 3
    (0 + 0) + 0 ≡ 0 + (0 + 0)   ...   (0 + 4) + 5 ≡ 0 + (4 + 5)   ...
    (1 + 0) + 0 ≡ 1 + (0 + 0)   ...   (1 + 4) + 5 ≡ 1 + (4 + 5)   ...
    (2 + 0) + 0 ≡ 2 + (0 + 0)   ...   (2 + 4) + 5 ≡ 2 + (4 + 5)   ...
    (3 + 0) + 0 ≡ 3 + (0 + 0)   ...   (3 + 4) + 5 ≡ 3 + (4 + 5)   ...

The process continues.  On the *m*th day we will know all the
judgements where the first number is less than *m*.

There is also a completely finite approach to generating the same equations,
which is left as an exercise for the reader.

### Exercise `+-assoc-finite`

Write out what is known about associativity on each of the first four
days using a finite story of creation, as
[earlier](Naturals/index.html#finite-creation).


## Associativity with rewrite

There is more than one way to skin a cat.  Here is a second proof of
associativity of addition in Agda, using `rewrite` rather than chains of
equations.
<pre class="Agda">{% raw %}<a id="+-assoc′"></a><a id="16713" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#16713" class="Function">+-assoc′</a> <a id="16722" class="Symbol">:</a> <a id="16724" class="Symbol">∀</a> <a id="16726" class="Symbol">(</a><a id="16727" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#16727" class="Bound">m</a> <a id="16729" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#16729" class="Bound">n</a> <a id="16731" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#16731" class="Bound">p</a> <a id="16733" class="Symbol">:</a> <a id="16735" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="16736" class="Symbol">)</a> <a id="16738" class="Symbol">→</a> <a id="16740" class="Symbol">(</a><a id="16741" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#16727" class="Bound">m</a> <a id="16743" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16745" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#16729" class="Bound">n</a><a id="16746" class="Symbol">)</a> <a id="16748" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16750" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#16731" class="Bound">p</a> <a id="16752" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="16754" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#16727" class="Bound">m</a> <a id="16756" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16758" class="Symbol">(</a><a id="16759" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#16729" class="Bound">n</a> <a id="16761" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16763" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#16731" class="Bound">p</a><a id="16764" class="Symbol">)</a>
<a id="16766" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#16713" class="Function">+-assoc′</a> <a id="16775" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="16780" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#16780" class="Bound">n</a> <a id="16782" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#16782" class="Bound">p</a> <a id="16784" class="Symbol">=</a> <a id="16786" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>
<a id="16791" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#16713" class="Function">+-assoc′</a> <a id="16800" class="Symbol">(</a><a id="16801" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="16805" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#16805" class="Bound">m</a><a id="16806" class="Symbol">)</a> <a id="16808" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#16808" class="Bound">n</a> <a id="16810" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#16810" class="Bound">p</a> <a id="16812" class="Keyword">rewrite</a> <a id="16820" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#16713" class="Function">+-assoc′</a> <a id="16829" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#16805" class="Bound">m</a> <a id="16831" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#16808" class="Bound">n</a> <a id="16833" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#16810" class="Bound">p</a> <a id="16835" class="Symbol">=</a> <a id="16837" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>{% endraw %}</pre>

For the base case, we must show:

    (zero + n) + p ≡ zero + (n + p)

Simplifying both sides with the base case of addition yields the equation:

    n + p ≡ n + p

This holds trivially. The proof that a term is equal to itself is written `refl`.

For the inductive case, we must show:

    (suc m + n) + p ≡ suc m + (n + p)

Simplifying both sides with the inductive case of addition yields the equation:

    suc ((m + n) + p) ≡ suc (m + (n + p))

After rewriting with the inductive hypothesis these two terms are equal, and the
proof is again given by `refl`.  Rewriting by a given equation is indicated by
the keyword `rewrite` followed by a proof of that equation.  Rewriting avoids
not only chains of equations but also the need to invoke `cong`.


## Commutativity with rewrite

Here is a second proof of commutativity of addition, using `rewrite` rather than
chains of equations.
<pre class="Agda">{% raw %}<a id="+-identity′"></a><a id="17756" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#17756" class="Function">+-identity′</a> <a id="17768" class="Symbol">:</a> <a id="17770" class="Symbol">∀</a> <a id="17772" class="Symbol">(</a><a id="17773" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#17773" class="Bound">n</a> <a id="17775" class="Symbol">:</a> <a id="17777" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="17778" class="Symbol">)</a> <a id="17780" class="Symbol">→</a> <a id="17782" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#17773" class="Bound">n</a> <a id="17784" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="17786" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="17791" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="17793" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#17773" class="Bound">n</a>
<a id="17795" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#17756" class="Function">+-identity′</a> <a id="17807" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="17812" class="Symbol">=</a> <a id="17814" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>
<a id="17819" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#17756" class="Function">+-identity′</a> <a id="17831" class="Symbol">(</a><a id="17832" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="17836" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#17836" class="Bound">n</a><a id="17837" class="Symbol">)</a> <a id="17839" class="Keyword">rewrite</a> <a id="17847" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#17756" class="Function">+-identity′</a> <a id="17859" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#17836" class="Bound">n</a> <a id="17861" class="Symbol">=</a> <a id="17863" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>

<a id="+-suc′"></a><a id="17869" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#17869" class="Function">+-suc′</a> <a id="17876" class="Symbol">:</a> <a id="17878" class="Symbol">∀</a> <a id="17880" class="Symbol">(</a><a id="17881" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#17881" class="Bound">m</a> <a id="17883" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#17883" class="Bound">n</a> <a id="17885" class="Symbol">:</a> <a id="17887" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="17888" class="Symbol">)</a> <a id="17890" class="Symbol">→</a> <a id="17892" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#17881" class="Bound">m</a> <a id="17894" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="17896" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="17900" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#17883" class="Bound">n</a> <a id="17902" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="17904" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="17908" class="Symbol">(</a><a id="17909" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#17881" class="Bound">m</a> <a id="17911" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="17913" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#17883" class="Bound">n</a><a id="17914" class="Symbol">)</a>
<a id="17916" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#17869" class="Function">+-suc′</a> <a id="17923" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="17928" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#17928" class="Bound">n</a> <a id="17930" class="Symbol">=</a> <a id="17932" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>
<a id="17937" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#17869" class="Function">+-suc′</a> <a id="17944" class="Symbol">(</a><a id="17945" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="17949" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#17949" class="Bound">m</a><a id="17950" class="Symbol">)</a> <a id="17952" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#17952" class="Bound">n</a> <a id="17954" class="Keyword">rewrite</a> <a id="17962" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#17869" class="Function">+-suc′</a> <a id="17969" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#17949" class="Bound">m</a> <a id="17971" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#17952" class="Bound">n</a> <a id="17973" class="Symbol">=</a> <a id="17975" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>

<a id="+-comm′"></a><a id="17981" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#17981" class="Function">+-comm′</a> <a id="17989" class="Symbol">:</a> <a id="17991" class="Symbol">∀</a> <a id="17993" class="Symbol">(</a><a id="17994" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#17994" class="Bound">m</a> <a id="17996" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#17996" class="Bound">n</a> <a id="17998" class="Symbol">:</a> <a id="18000" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="18001" class="Symbol">)</a> <a id="18003" class="Symbol">→</a> <a id="18005" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#17994" class="Bound">m</a> <a id="18007" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="18009" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#17996" class="Bound">n</a> <a id="18011" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="18013" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#17996" class="Bound">n</a> <a id="18015" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="18017" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#17994" class="Bound">m</a>
<a id="18019" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#17981" class="Function">+-comm′</a> <a id="18027" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#18027" class="Bound">m</a> <a id="18029" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="18034" class="Keyword">rewrite</a> <a id="18042" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#17756" class="Function">+-identity′</a> <a id="18054" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#18027" class="Bound">m</a> <a id="18056" class="Symbol">=</a> <a id="18058" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>
<a id="18063" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#17981" class="Function">+-comm′</a> <a id="18071" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#18071" class="Bound">m</a> <a id="18073" class="Symbol">(</a><a id="18074" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="18078" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#18078" class="Bound">n</a><a id="18079" class="Symbol">)</a> <a id="18081" class="Keyword">rewrite</a> <a id="18089" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#17869" class="Function">+-suc′</a> <a id="18096" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#18071" class="Bound">m</a> <a id="18098" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#18078" class="Bound">n</a> <a id="18100" class="Symbol">|</a> <a id="18102" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#17981" class="Function">+-comm′</a> <a id="18110" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#18071" class="Bound">m</a> <a id="18112" href="{% endraw %}{{ site.baseurl }}{% link out/Properties.md %}{% raw %}#18078" class="Bound">n</a> <a id="18114" class="Symbol">=</a> <a id="18116" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>{% endraw %}</pre>
In the final line, rewriting with two equations is
indicated by separating the two proofs of the relevant equations by a
vertical bar; the rewrite on the left is performed before that on the
right.


## Building proofs interactively

It is instructive to see how to build the alternative proof of
associativity using the interactive features of Agda in Emacs.
Begin by typing

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ m n p = ?

The question mark indicates that you would like Agda to help with
filling in that part of the code.  If you type `^C ^L` (control-C
followed by control-L), the question mark will be replaced.

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ m n p = { }0

The empty braces are called a *hole*, and 0 is a number used for
referring to the hole.  The hole may display highlighted in green.
Emacs will also create a new window at the bottom of the screen
displaying the text

    ?0 : ((m + n) + p) ≡ (m + (n + p))

This indicates that hole 0 is to be filled in with a proof of
the stated judgement.

We wish to prove the proposition by induction on `m`.  Move
the cursor into the hole and type `^C ^C`.  You will be given
the prompt:

    pattern variables to case (empty for split on result):

Typing `m` will cause a split on that variable, resulting
in an update to the code.

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = { }0
    +-assoc′ (suc m) n p = { }1

There are now two holes, and the window at the bottom tells you what
each is required to prove:

    ?0 : ((zero + n) + p) ≡ (zero + (n + p))
    ?1 : ((suc m + n) + p) ≡ (suc m + (n + p))

Going into hole 0 and typing `^C ^,` will display the text:

    Goal: (n + p) ≡ (n + p)
    ————————————————————————————————————————————————————————————
    p : ℕ
    n : ℕ

This indicates that after simplification the goal for hole 0 is as
stated, and that variables `p` and `n` of the stated types are
available to use in the proof.  The proof of the given goal is
trivial, and going into the goal and typing `^C ^R` will fill it in,
renumbering the remaining hole to 0:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = refl
    +-assoc′ (suc m) n p = { }0

Going into the new hole 0 and typing `^C ^,` will display the text:

    Goal: suc ((m + n) + p) ≡ suc (m + (n + p))
    ————————————————————————————————————————————————————————————
    p : ℕ
    n : ℕ
    m : ℕ

Again, this gives the simplified goal and the available variables.
In this case, we need to rewrite by the induction
hypothesis, so let's edit the text accordingly:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = refl
    +-assoc′ (suc m) n p rewrite +-assoc′ m n p = { }0

Going into the remaining hole and typing `^C ^,` will display the text:

    Goal: suc (m + (n + p)) ≡ suc (m + (n + p))
    ————————————————————————————————————————————————————————————
    p : ℕ
    n : ℕ
    m : ℕ

The proof of the given goal is trivial, and going into the goal and
typing `^C ^R` will fill it in, completing the proof:

    +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
    +-assoc′ zero n p = refl
    +-assoc′ (suc m) n p rewrite +-assoc′ m n p = refl


### Exercise (`+-swap`)

Show

    m + (n + p) ≡ n + (m + p)

for all naturals `m`, `n`, and `p`. No induction is needed,
just apply the previous results which show addition
is associative and commutative.  You may need to use
the following function from the standard library:

    sym : ∀ {m n : ℕ} → m ≡ n → n ≡ m

### Exercise (`*-distrib-+`)

Show multiplication distributes over addition, that is,

    (m + n) * p ≡ m * p + n * p

for all naturals `m`, `n`, and `p`.

### Exercise (`*-assoc`)

Show multiplication is associative, that is,

    (m * n) * p ≡ m * (n * p)

for all naturals `m`, `n`, and `p`.

### Exercise (`*-comm`)

Show multiplication is commutative, that is,

    m * n ≡ n * m

for all naturals `m` and `n`.  As with commutativity of addition,
you will need to formulate and prove suitable lemmas.

### Exercise (`0∸n≡0`)

Show

    zero ∸ n ≡ zero

for all naturals `n`. Did your proof require induction?

### Exercise (`∸-+-assoc`)

Show that monus associates with addition, that is,

    m ∸ n ∸ p ≡ m ∸ (n + p)

for all naturals `m`, `n`, and `p`.

## Standard library

Definitions similar to those in this chapter can be found in the standard library.
<pre class="Agda">{% raw %}<a id="22592" class="Keyword">import</a> <a id="22599" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="22619" class="Keyword">using</a> <a id="22625" class="Symbol">(</a><a id="22626" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#7768" class="Function">+-assoc</a><a id="22633" class="Symbol">;</a> <a id="22635" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#7924" class="Function">+-identityʳ</a><a id="22646" class="Symbol">;</a> <a id="22648" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#7665" class="Function">+-suc</a><a id="22653" class="Symbol">;</a> <a id="22655" href="https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#8101" class="Function">+-comm</a><a id="22661" class="Symbol">)</a>{% endraw %}</pre>

## Unicode

This chapter uses the following unicode.

    ∀  U+2200  FOR ALL (\forall)
    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)
    ′  U+2032  PRIME (\')
    ″  U+2033  DOUBLE PRIME (\')
    ‴  U+2034  TRIPLE PRIME (\')
    ⁗  U+2057  QUADRUPLE PRIME (\')

Similar to `\r`, the command `\^r` gives access to a variety of
superscript rightward arrows, and also a superscript letter `r`.
The command `\'` gives access to a range of primes (`′ ″ ‴ ⁗`).
