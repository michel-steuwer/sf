---
title     : "Negation: Negation, with intuitionistic and classical logic"
layout    : page
permalink : /Negation
---

This chapter introduces negation, and discusses intuitionistic
and classical logic.

## Imports

<pre class="Agda">{% raw %}<a id="233" class="Keyword">open</a> <a id="238" class="Keyword">import</a> <a id="245" href="{% endraw %}{{ site.baseurl }}{% link out/Isomorphism.md %}{% raw %}" class="Module">Isomorphism</a> <a id="257" class="Keyword">using</a> <a id="263" class="Symbol">(</a><a id="264" href="{% endraw %}{{ site.baseurl }}{% link out/Isomorphism.md %}{% raw %}#1042" class="Record Operator">_≃_</a><a id="267" class="Symbol">;</a> <a id="269" href="{% endraw %}{{ site.baseurl }}{% link out/Isomorphism.md %}{% raw %}#4647" class="Function">≃-sym</a><a id="274" class="Symbol">;</a> <a id="276" href="{% endraw %}{{ site.baseurl }}{% link out/Isomorphism.md %}{% raw %}#4973" class="Function">≃-trans</a><a id="283" class="Symbol">;</a> <a id="285" href="{% endraw %}{{ site.baseurl }}{% link out/Isomorphism.md %}{% raw %}#6636" class="Record Operator">_≲_</a><a id="288" class="Symbol">)</a>
<a id="290" class="Keyword">open</a> <a id="295" class="Keyword">import</a> <a id="302" href="https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="340" class="Keyword">using</a> <a id="346" class="Symbol">(</a><a id="347" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">_≡_</a><a id="350" class="Symbol">;</a> <a id="352" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="356" class="Symbol">)</a>
<a id="358" class="Keyword">open</a> <a id="363" class="Keyword">import</a> <a id="370" href="https://agda.github.io/agda-stdlib/Data.Nat.html" class="Module">Data.Nat</a> <a id="379" class="Keyword">using</a> <a id="385" class="Symbol">(</a><a id="386" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="387" class="Symbol">;</a> <a id="389" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="393" class="Symbol">;</a> <a id="395" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a><a id="398" class="Symbol">)</a>
<a id="400" class="Keyword">open</a> <a id="405" class="Keyword">import</a> <a id="412" href="https://agda.github.io/agda-stdlib/Data.Empty.html" class="Module">Data.Empty</a> <a id="423" class="Keyword">using</a> <a id="429" class="Symbol">(</a><a id="430" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype">⊥</a><a id="431" class="Symbol">;</a> <a id="433" href="https://agda.github.io/agda-stdlib/Data.Empty.html#360" class="Function">⊥-elim</a><a id="439" class="Symbol">)</a>
<a id="441" class="Keyword">open</a> <a id="446" class="Keyword">import</a> <a id="453" href="https://agda.github.io/agda-stdlib/Data.Sum.html" class="Module">Data.Sum</a> <a id="462" class="Keyword">using</a> <a id="468" class="Symbol">(</a><a id="469" href="https://agda.github.io/agda-stdlib/Data.Sum.html#508" class="Datatype Operator">_⊎_</a><a id="472" class="Symbol">;</a> <a id="474" href="https://agda.github.io/agda-stdlib/Data.Sum.html#564" class="InductiveConstructor">inj₁</a><a id="478" class="Symbol">;</a> <a id="480" href="https://agda.github.io/agda-stdlib/Data.Sum.html#589" class="InductiveConstructor">inj₂</a><a id="484" class="Symbol">)</a>
<a id="486" class="Keyword">open</a> <a id="491" class="Keyword">import</a> <a id="498" href="https://agda.github.io/agda-stdlib/Data.Product.html" class="Module">Data.Product</a> <a id="511" class="Keyword">using</a> <a id="517" class="Symbol">(</a><a id="518" href="https://agda.github.io/agda-stdlib/Data.Product.html#1329" class="Function Operator">_×_</a><a id="521" class="Symbol">;</a> <a id="523" href="https://agda.github.io/agda-stdlib/Data.Product.html#559" class="Field">proj₁</a><a id="528" class="Symbol">;</a> <a id="530" href="https://agda.github.io/agda-stdlib/Data.Product.html#573" class="Field">proj₂</a><a id="535" class="Symbol">)</a> <a id="537" class="Keyword">renaming</a> <a id="546" class="Symbol">(</a><a id="547" href="https://agda.github.io/agda-stdlib/Data.Product.html#543" class="InductiveConstructor Operator">_,_</a> <a id="551" class="Symbol">to</a> <a id="554" href="https://agda.github.io/agda-stdlib/Data.Product.html#543" class="InductiveConstructor Operator">⟨_,_⟩</a><a id="559" class="Symbol">)</a>
<a id="561" class="Keyword">open</a> <a id="566" class="Keyword">import</a> <a id="573" href="https://agda.github.io/agda-stdlib/Function.html" class="Module">Function</a> <a id="582" class="Keyword">using</a> <a id="588" class="Symbol">(</a><a id="589" href="https://agda.github.io/agda-stdlib/Function.html#748" class="Function Operator">_∘_</a><a id="592" class="Symbol">)</a>{% endraw %}</pre>


## Negation

Given a proposition `A`, the negation `¬ A` holds if `A` cannot hold.
We formalise this idea by declaring negation to be the same
as implication of false. 
<pre class="Agda">{% raw %}<a id="¬_"></a><a id="789" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#789" class="Function Operator">¬_</a> <a id="792" class="Symbol">:</a> <a id="794" class="PrimitiveType">Set</a> <a id="798" class="Symbol">→</a> <a id="800" class="PrimitiveType">Set</a>
<a id="804" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#789" class="Function Operator">¬</a> <a id="806" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#806" class="Bound">A</a> <a id="808" class="Symbol">=</a> <a id="810" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#806" class="Bound">A</a> <a id="812" class="Symbol">→</a> <a id="814" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype">⊥</a>{% endraw %}</pre>
This is a form of *proof by contradiction*: if assuming `A` leads
to the conclusion `⊥` (a contradiction), then we must have `¬ A`.

Evidence that `¬ A` holds is of the form

    λ{ x → N }

where `N` is a term of type `⊥` containing as a free variable `x` of type `A`.
In other words, evidence that `¬ A` holds is a function that converts evidence
that `A` holds into evidence that `⊥` holds.

Given evidence that both `¬ A` and `A` hold, we can conclude that `⊥` holds.
In other words, if both `¬ A` and `A` hold, then we have a contradiction.
<pre class="Agda">{% raw %}<a id="¬-elim"></a><a id="1386" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#1386" class="Function">¬-elim</a> <a id="1393" class="Symbol">:</a> <a id="1395" class="Symbol">∀</a> <a id="1397" class="Symbol">{</a><a id="1398" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#1398" class="Bound">A</a> <a id="1400" class="Symbol">:</a> <a id="1402" class="PrimitiveType">Set</a><a id="1405" class="Symbol">}</a> <a id="1407" class="Symbol">→</a> <a id="1409" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#789" class="Function Operator">¬</a> <a id="1411" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#1398" class="Bound">A</a> <a id="1413" class="Symbol">→</a> <a id="1415" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#1398" class="Bound">A</a> <a id="1417" class="Symbol">→</a> <a id="1419" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype">⊥</a>
<a id="1421" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#1386" class="Function">¬-elim</a> <a id="1428" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#1428" class="Bound">¬x</a> <a id="1431" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#1431" class="Bound">x</a> <a id="1433" class="Symbol">=</a> <a id="1435" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#1428" class="Bound">¬x</a> <a id="1438" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#1431" class="Bound">x</a>{% endraw %}</pre>
Here we write `¬x` for evidence of `¬ A` and `x` for evidence of `A`.  This
means that `¬x` must be a function of type `A → ⊥`, and hence the application
`¬x x` must be of type `⊥`.  Note that this rule is just a special case of `→-elim`.

We set the precedence of negation so that it binds more tightly
than disjunction and conjunction, but less tightly than anything else.
<pre class="Agda">{% raw %}<a id="1839" class="Keyword">infix</a> <a id="1845" class="Number">3</a> <a id="1847" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#789" class="Function Operator">¬_</a>{% endraw %}</pre>
Thus, `¬ A × ¬ B` parses as `(¬ A) × (¬ B)` and `¬ m ≡ n` as `¬ (m ≡ n)`.

In *classical* logic, we have that `A` is equivalent to `¬ ¬ A`.
As we discuss below, in Agda we use *intuitionistic* logic, where
we have only half of this equivalence, namely that `A` implies `¬ ¬ A`.
<pre class="Agda">{% raw %}<a id="¬¬-intro"></a><a id="2152" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#2152" class="Function">¬¬-intro</a> <a id="2161" class="Symbol">:</a> <a id="2163" class="Symbol">∀</a> <a id="2165" class="Symbol">{</a><a id="2166" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#2166" class="Bound">A</a> <a id="2168" class="Symbol">:</a> <a id="2170" class="PrimitiveType">Set</a><a id="2173" class="Symbol">}</a> <a id="2175" class="Symbol">→</a> <a id="2177" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#2166" class="Bound">A</a> <a id="2179" class="Symbol">→</a> <a id="2181" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#789" class="Function Operator">¬</a> <a id="2183" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#789" class="Function Operator">¬</a> <a id="2185" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#2166" class="Bound">A</a>
<a id="2187" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#2152" class="Function">¬¬-intro</a> <a id="2196" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#2196" class="Bound">x</a> <a id="2198" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#2198" class="Bound">¬x</a> <a id="2201" class="Symbol">=</a> <a id="2203" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#2198" class="Bound">¬x</a> <a id="2206" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#2196" class="Bound">x</a>{% endraw %}</pre>
Let `x` be evidence of `A`. We will show that assuming
`¬ A` leads to a contradiction, and hence `¬ ¬ A` must hold.
Let `¬x` be evidence of `¬ A`.  Then from `A` and `¬ A`
we have a contradiction, evidenced by `¬x x`.  Hence, we have
shown `¬ ¬ A`.

We cannot show that `¬ ¬ A` implies `A`, but we can show that
`¬ ¬ ¬ A` implies `¬ A`.
<pre class="Agda">{% raw %}<a id="¬¬¬-elim"></a><a id="2569" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#2569" class="Function">¬¬¬-elim</a> <a id="2578" class="Symbol">:</a> <a id="2580" class="Symbol">∀</a> <a id="2582" class="Symbol">{</a><a id="2583" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#2583" class="Bound">A</a> <a id="2585" class="Symbol">:</a> <a id="2587" class="PrimitiveType">Set</a><a id="2590" class="Symbol">}</a> <a id="2592" class="Symbol">→</a> <a id="2594" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#789" class="Function Operator">¬</a> <a id="2596" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#789" class="Function Operator">¬</a> <a id="2598" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#789" class="Function Operator">¬</a> <a id="2600" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#2583" class="Bound">A</a> <a id="2602" class="Symbol">→</a> <a id="2604" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#789" class="Function Operator">¬</a> <a id="2606" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#2583" class="Bound">A</a>
<a id="2608" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#2569" class="Function">¬¬¬-elim</a> <a id="2617" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#2617" class="Bound">¬¬¬x</a> <a id="2622" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#2622" class="Bound">x</a> <a id="2624" class="Symbol">=</a> <a id="2626" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#2617" class="Bound">¬¬¬x</a> <a id="2631" class="Symbol">(</a><a id="2632" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#2152" class="Function">¬¬-intro</a> <a id="2641" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#2622" class="Bound">x</a><a id="2642" class="Symbol">)</a>{% endraw %}</pre>
Let `¬¬¬x` be evidence of `¬ ¬ ¬ A`. We will show that assuming
`A` leads to a contradiction, and hence `¬ A` must hold.
Let `x` be evidence of `A`. Then by the previous result, we
can conclude `¬ ¬ A`, evidenced by `¬¬-intro x`.  Then from
`¬ ¬ ¬ A` and `¬ ¬ A` we have a contradiction, evidenced by
`¬¬¬x (¬¬-intro x)`.  Hence we have shown `¬ A`.

Another law of logic is *contraposition*,
stating that if `A` implies `B`, then `¬ B` implies `¬ A`.
<pre class="Agda">{% raw %}<a id="contraposition"></a><a id="3120" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#3120" class="Function">contraposition</a> <a id="3135" class="Symbol">:</a> <a id="3137" class="Symbol">∀</a> <a id="3139" class="Symbol">{</a><a id="3140" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#3140" class="Bound">A</a> <a id="3142" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#3142" class="Bound">B</a> <a id="3144" class="Symbol">:</a> <a id="3146" class="PrimitiveType">Set</a><a id="3149" class="Symbol">}</a> <a id="3151" class="Symbol">→</a> <a id="3153" class="Symbol">(</a><a id="3154" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#3140" class="Bound">A</a> <a id="3156" class="Symbol">→</a> <a id="3158" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#3142" class="Bound">B</a><a id="3159" class="Symbol">)</a> <a id="3161" class="Symbol">→</a> <a id="3163" class="Symbol">(</a><a id="3164" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#789" class="Function Operator">¬</a> <a id="3166" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#3142" class="Bound">B</a> <a id="3168" class="Symbol">→</a> <a id="3170" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#789" class="Function Operator">¬</a> <a id="3172" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#3140" class="Bound">A</a><a id="3173" class="Symbol">)</a>
<a id="3175" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#3120" class="Function">contraposition</a> <a id="3190" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#3190" class="Bound">f</a> <a id="3192" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#3192" class="Bound">¬y</a> <a id="3195" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#3195" class="Bound">x</a> <a id="3197" class="Symbol">=</a> <a id="3199" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#3192" class="Bound">¬y</a> <a id="3202" class="Symbol">(</a><a id="3203" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#3190" class="Bound">f</a> <a id="3205" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#3195" class="Bound">x</a><a id="3206" class="Symbol">)</a>{% endraw %}</pre>
Let `f` be evidence of `A → B` and let `¬y` be evidence of `¬ B`.  We
will show that assuming `A` leads to a contradiction, and hence
`¬ A` must hold. Let `x` be evidence of `A`.  Then from `A → B` and
`A` we may conclude `B`, evidenced by `f x`, and from `B` and `¬ B`
we may conclude `⊥`, evidenced by `¬y (f x)`.  Hence, we have shown
`¬ A`.

Using negation, it is straightforward to define inequality.
<pre class="Agda">{% raw %}<a id="_≢_"></a><a id="3638" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#3638" class="Function Operator">_≢_</a> <a id="3642" class="Symbol">:</a> <a id="3644" class="Symbol">∀</a> <a id="3646" class="Symbol">{</a><a id="3647" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#3647" class="Bound">A</a> <a id="3649" class="Symbol">:</a> <a id="3651" class="PrimitiveType">Set</a><a id="3654" class="Symbol">}</a> <a id="3656" class="Symbol">→</a> <a id="3658" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#3647" class="Bound">A</a> <a id="3660" class="Symbol">→</a> <a id="3662" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#3647" class="Bound">A</a> <a id="3664" class="Symbol">→</a> <a id="3666" class="PrimitiveType">Set</a>
<a id="3670" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#3670" class="Bound">x</a> <a id="3672" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#3638" class="Function Operator">≢</a> <a id="3674" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#3674" class="Bound">y</a>  <a id="3677" class="Symbol">=</a>  <a id="3680" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#789" class="Function Operator">¬</a> <a id="3682" class="Symbol">(</a><a id="3683" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#3670" class="Bound">x</a> <a id="3685" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="3687" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#3674" class="Bound">y</a><a id="3688" class="Symbol">)</a>{% endraw %}</pre>
It is straightforward to show distinct numbers are not equal.
<pre class="Agda">{% raw %}<a id="3776" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#3776" class="Function">_</a> <a id="3778" class="Symbol">:</a> <a id="3780" class="Number">1</a> <a id="3782" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#3638" class="Function Operator">≢</a> <a id="3784" class="Number">2</a>
<a id="3786" class="Symbol">_</a> <a id="3788" class="Symbol">=</a> <a id="3790" class="Symbol">λ()</a>{% endraw %}</pre>
This is our first use of an absurd pattern in a lambda expression.
The type `M ≡ N` is occupied exactly when `M` and `N` simplify to
identical terms. Since `1` and `2` simplify to distinct normal forms,
Agda determines that there is no possible evidence that `1 ≡ 2`.
As a second example, it is also easy to validate
Peano's postulate that zero is not the successor of any number.
<pre class="Agda">{% raw %}<a id="peano"></a><a id="4199" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#4199" class="Function">peano</a> <a id="4205" class="Symbol">:</a> <a id="4207" class="Symbol">∀</a> <a id="4209" class="Symbol">{</a><a id="4210" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#4210" class="Bound">m</a> <a id="4212" class="Symbol">:</a> <a id="4214" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="4215" class="Symbol">}</a> <a id="4217" class="Symbol">→</a> <a id="4219" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="4224" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#3638" class="Function Operator">≢</a> <a id="4226" href="https://agda.github.io/agda-stdlib/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="4230" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#4210" class="Bound">m</a>
<a id="4232" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#4199" class="Function">peano</a> <a id="4238" class="Symbol">=</a> <a id="4240" class="Symbol">λ()</a>{% endraw %}</pre>
The evidence is essentially the same, as the absurd pattern matches
all possible evidence of type `zero ≡ suc m`. 

Given the correspondence of implication to exponentiation and
false to the type with no members, we can view negation as
raising to the zero power.  This indeed corresponds to what
we know for arithmetic, where

    0 ^ n  =  1,  if n = 0
           =  0,  if n ≠ 0

Indeed, there is exactly one proof of `⊥ → ⊥`.
<pre class="Agda">{% raw %}<a id="id"></a><a id="4698" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#4698" class="Function">id</a> <a id="4701" class="Symbol">:</a> <a id="4703" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype">⊥</a> <a id="4705" class="Symbol">→</a> <a id="4707" href="https://agda.github.io/agda-stdlib/Data.Empty.html#243" class="Datatype">⊥</a>
<a id="4709" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#4698" class="Function">id</a> <a id="4712" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#4712" class="Bound">x</a> <a id="4714" class="Symbol">=</a> <a id="4716" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#4712" class="Bound">x</a>{% endraw %}</pre>
However, there are no possible values of type `ℕ → ⊥`,
or indeed of type `A → ⊥` when `A` is anything other than `⊥` itself.


### Exercise (`⊎-dual-×`)

Show that conjunction, disjunction, and negation are related by a
version of De Morgan's Law.
<pre class="Agda">{% raw %}<a id="⊎-Dual-×"></a><a id="4990" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#4990" class="Function">⊎-Dual-×</a> <a id="4999" class="Symbol">:</a> <a id="5001" class="PrimitiveType">Set₁</a>
<a id="5006" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#4990" class="Function">⊎-Dual-×</a> <a id="5015" class="Symbol">=</a> <a id="5017" class="Symbol">∀</a> <a id="5019" class="Symbol">{</a><a id="5020" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#5020" class="Bound">A</a> <a id="5022" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#5022" class="Bound">B</a> <a id="5024" class="Symbol">:</a> <a id="5026" class="PrimitiveType">Set</a><a id="5029" class="Symbol">}</a> <a id="5031" class="Symbol">→</a> <a id="5033" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#789" class="Function Operator">¬</a> <a id="5035" class="Symbol">(</a><a id="5036" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#5020" class="Bound">A</a> <a id="5038" href="https://agda.github.io/agda-stdlib/Data.Sum.html#508" class="Datatype Operator">⊎</a> <a id="5040" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#5022" class="Bound">B</a><a id="5041" class="Symbol">)</a> <a id="5043" href="{% endraw %}{{ site.baseurl }}{% link out/Isomorphism.md %}{% raw %}#1042" class="Record Operator">≃</a> <a id="5045" class="Symbol">(</a><a id="5046" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#789" class="Function Operator">¬</a> <a id="5048" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#5020" class="Bound">A</a><a id="5049" class="Symbol">)</a> <a id="5051" href="https://agda.github.io/agda-stdlib/Data.Product.html#1329" class="Function Operator">×</a> <a id="5053" class="Symbol">(</a><a id="5054" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#789" class="Function Operator">¬</a> <a id="5056" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#5022" class="Bound">B</a><a id="5057" class="Symbol">)</a>{% endraw %}</pre>
Show there is a term of type `⊎-Dual-×`.
This result is an easy consequence of something we've proved previously.

Is there also a term of the following type?
<pre class="Agda">{% raw %}<a id="×-Dual-⊎"></a><a id="5242" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#5242" class="Function">×-Dual-⊎</a> <a id="5251" class="Symbol">:</a> <a id="5253" class="PrimitiveType">Set₁</a>
<a id="5258" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#5242" class="Function">×-Dual-⊎</a> <a id="5267" class="Symbol">=</a> <a id="5269" class="Symbol">∀</a> <a id="5271" class="Symbol">{</a><a id="5272" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#5272" class="Bound">A</a> <a id="5274" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#5274" class="Bound">B</a> <a id="5276" class="Symbol">:</a> <a id="5278" class="PrimitiveType">Set</a><a id="5281" class="Symbol">}</a> <a id="5283" class="Symbol">→</a> <a id="5285" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#789" class="Function Operator">¬</a> <a id="5287" class="Symbol">(</a><a id="5288" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#5272" class="Bound">A</a> <a id="5290" href="https://agda.github.io/agda-stdlib/Data.Product.html#1329" class="Function Operator">×</a> <a id="5292" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#5274" class="Bound">B</a><a id="5293" class="Symbol">)</a> <a id="5295" href="{% endraw %}{{ site.baseurl }}{% link out/Isomorphism.md %}{% raw %}#1042" class="Record Operator">≃</a> <a id="5297" class="Symbol">(</a><a id="5298" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#789" class="Function Operator">¬</a> <a id="5300" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#5272" class="Bound">A</a><a id="5301" class="Symbol">)</a> <a id="5303" href="https://agda.github.io/agda-stdlib/Data.Sum.html#508" class="Datatype Operator">⊎</a> <a id="5305" class="Symbol">(</a><a id="5306" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#789" class="Function Operator">¬</a> <a id="5308" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#5274" class="Bound">B</a><a id="5309" class="Symbol">)</a>{% endraw %}</pre>
If so, prove; if not, explain why.


## Intuitive and Classical logic

In Gilbert and Sullivan's *The Gondoliers*, Casilda is told that
as an infant she was married to the heir of the King of Batavia, but
that due to a mix-up no one knows which of two individuals, Marco or
Giuseppe, is the heir.  Alarmed, she wails "Then do you mean to say
that I am married to one of two gondoliers, but it is impossible to
say which?"  To which the response is "Without any doubt of any kind
whatever."

Logic comes in many varieties, and one distinction is between
*classical* and *intuitionistic*. Intuitionists, concerned
by cavalier assumptions made by some logicians about the nature of
infinity, insist upon a constructionist notion of truth.  In
particular, they insist that a proof of `A ⊎ B` must show
*which* of `A` or `B` holds, and hence they would reject the
claim that Casilda is married to Marco or Giuseppe until one of the
two was identified as her husband.  Perhaps Gilbert and Sullivan
anticipated intuitionism, for their story's outcome is that the heir
turns out to be a third individual, Luiz, with whom Casilda is,
conveniently, already in love.

Intuitionists also reject the law of the excluded
middle, which asserts `A ⊎ ¬ A` for every `A`, since the law
gives no clue as to *which* of `A` or `¬ A` holds. Heyting
formalised a variant of Hilbert's classical logic that captures the
intuitionistic notion of provability. In particular, the law of the
excluded middle is provable in Hilbert's logic, but not in Heyting's.
Further, if the law of the excluded middle is added as an axiom to
Heyting's logic, then it becomes equivalent to Hilbert's.
Kolmogorov
showed the two logics were closely related: he gave a double-negation
translation, such that a formula is provable in classical logic if and
only if its translation is provable in intuitionistic logic.

Propositions as Types was first formulated for intuitionistic logic.
It is a perfect fit, because in the intuitionist interpretation the
formula `A ⊎ B` is provable exactly when one exhibits either a proof
of `A` or a proof of `B`, so the type corresponding to disjunction is
a disjoint sum.

(Parts of the above are adopted from "Propositions as Types", Philip Wadler,
*Communications of the ACM*, December 2015.)

## Excluded middle is irrefutable

The law of the excluded middle can be formulated as follows.
<pre class="Agda">{% raw %}<a id="EM"></a><a id="7719" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#7719" class="Function">EM</a> <a id="7722" class="Symbol">:</a> <a id="7724" class="PrimitiveType">Set₁</a>
<a id="7729" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#7719" class="Function">EM</a> <a id="7732" class="Symbol">=</a> <a id="7734" class="Symbol">∀</a> <a id="7736" class="Symbol">{</a><a id="7737" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#7737" class="Bound">A</a> <a id="7739" class="Symbol">:</a> <a id="7741" class="PrimitiveType">Set</a><a id="7744" class="Symbol">}</a> <a id="7746" class="Symbol">→</a> <a id="7748" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#7737" class="Bound">A</a> <a id="7750" href="https://agda.github.io/agda-stdlib/Data.Sum.html#508" class="Datatype Operator">⊎</a> <a id="7752" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#789" class="Function Operator">¬</a> <a id="7754" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#7737" class="Bound">A</a>{% endraw %}</pre>
As we noted, the law of the excluded middle does not hold in
intuitionistic logic.  However, we can show that it is *irrefutable*,
meaning that the negation of its negation is provable (and hence that
its negation is never provable).
<pre class="Agda">{% raw %}<a id="em-irrefutable"></a><a id="8014" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#8014" class="Function">em-irrefutable</a> <a id="8029" class="Symbol">:</a> <a id="8031" class="Symbol">∀</a> <a id="8033" class="Symbol">{</a><a id="8034" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#8034" class="Bound">A</a> <a id="8036" class="Symbol">:</a> <a id="8038" class="PrimitiveType">Set</a><a id="8041" class="Symbol">}</a> <a id="8043" class="Symbol">→</a> <a id="8045" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#789" class="Function Operator">¬</a> <a id="8047" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#789" class="Function Operator">¬</a> <a id="8049" class="Symbol">(</a><a id="8050" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#8034" class="Bound">A</a> <a id="8052" href="https://agda.github.io/agda-stdlib/Data.Sum.html#508" class="Datatype Operator">⊎</a> <a id="8054" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#789" class="Function Operator">¬</a> <a id="8056" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#8034" class="Bound">A</a><a id="8057" class="Symbol">)</a>
<a id="8059" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#8014" class="Function">em-irrefutable</a> <a id="8074" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#8074" class="Bound">k</a> <a id="8076" class="Symbol">=</a> <a id="8078" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#8074" class="Bound">k</a> <a id="8080" class="Symbol">(</a><a id="8081" href="https://agda.github.io/agda-stdlib/Data.Sum.html#589" class="InductiveConstructor">inj₂</a> <a id="8086" class="Symbol">λ{</a> <a id="8089" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#8089" class="Bound">x</a> <a id="8091" class="Symbol">→</a> <a id="8093" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#8074" class="Bound">k</a> <a id="8095" class="Symbol">(</a><a id="8096" href="https://agda.github.io/agda-stdlib/Data.Sum.html#564" class="InductiveConstructor">inj₁</a> <a id="8101" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#8089" class="Bound">x</a><a id="8102" class="Symbol">)</a> <a id="8104" class="Symbol">})</a>{% endraw %}</pre>
The best way to explain this code is to develop it interactively.

    em-irrefutable k = ?

Given evidence `k` that `¬ (A ⊎ ¬ A)`, that is, a function that give a
value of type `A ⊎ ¬ A` returns a value of the empty type, we must fill
in `?` with a term that returns a value of the empty type.  The only way
we can get a value of the empty type is by applying `k` itself, so let's
expand the hole accordingly.

    em-irrefutable k = k ?

We need to fill the new hole with a value of type `A ⊎ ¬ A`. We don't have
a value of type `A` to hand, so let's pick the second disjunct.

    em-irrefutable k = k (inj₂ λ{ x → ? })

The second disjunct accepts evidence of `¬ A`, that is, a function
that given a value of type `A` returns a value of the empty type.  We
bind `x` to the value of type `A`, and now we need to fill in the hole
with a value of the empty type.  Once again, he only way we can get a
value of the empty type is by applying `k` itself, so let's expand the
hole accordingly.

    em-irrefutable k = k (inj₂ λ{ x → k ? })

This time we do have a value of type `A` to hand, namely `x`, so we can
pick the first disjunct.

    em-irrefutable k = k (inj₂ λ{ x → k (inj₁ x) })

There are no holes left! This completes the proof. 

The following story illustrates the behaviour of the term we have created.
(With apologies to Peter Selinger, who tells a similar story
about a king, a wizard, and the Philosopher's stone.)

Once upon a time, the devil approached a man and made an offer:
"Either (a) I will give you one billion dollars, or (b) I will grant
you any wish if you pay me one billion dollars.
Of course, I get to choose whether I offer (a) or (b)."

The man was wary.  Did he need to sign over his soul?
No, said the devil, all the man need do is accept the offer.

The man pondered.  If he was offered (b) it was unlikely that he would
ever be able to buy the wish, but what was the harm in having the
opportunity available?

"I accept," said the man at last.  "Do I get (a) or (b)?"

The devil paused.  "I choose (b)."

The man was disappointed but not surprised.  That was that, he thought.
But the offer gnawed at him.  Imagine what he could do with his wish!
Many years passed, and the man began to accumulate money.  To get the
money he sometimes did bad things, and dimly he realised that
this must be what the devil had in mind.
Eventually he had his billion dollars, and the devil appeared again.

"Here is a billion dollars," said the man, handing over a valise
containing the money.  "Grant me my wish!"

The devil took possession of the valise.  Then he said, "Oh, did I say
(b) before?  I'm so sorry.  I meant (a).  It is my great pleasure to
give you one billion dollars."

And the devil handed back to the man the same valise that the man had
just handed to him.

(Parts of the above are adopted from "Call-by-Value is Dual to Call-by-Name",
Philip Wadler, *International Conference on Functional Programming*, 2003.)


### Exercise

Prove the following four formulas are equivalent to each other,
and to the formula `EM` given earlier.
<pre class="Agda">{% raw %}<a id="¬¬-Elim"></a><a id="11204" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11204" class="Function">¬¬-Elim</a> <a id="Peirce"></a><a id="11212" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11212" class="Function">Peirce</a> <a id="Implication"></a><a id="11219" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11219" class="Function">Implication</a> <a id="11231" class="Symbol">:</a> <a id="11233" class="PrimitiveType">Set₁</a>
<a id="11238" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11204" class="Function">¬¬-Elim</a> <a id="11246" class="Symbol">=</a> <a id="11248" class="Symbol">∀</a> <a id="11250" class="Symbol">{</a><a id="11251" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11251" class="Bound">A</a> <a id="11253" class="Symbol">:</a> <a id="11255" class="PrimitiveType">Set</a><a id="11258" class="Symbol">}</a> <a id="11260" class="Symbol">→</a> <a id="11262" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#789" class="Function Operator">¬</a> <a id="11264" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#789" class="Function Operator">¬</a> <a id="11266" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11251" class="Bound">A</a> <a id="11268" class="Symbol">→</a> <a id="11270" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11251" class="Bound">A</a>
<a id="11272" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11212" class="Function">Peirce</a> <a id="11279" class="Symbol">=</a> <a id="11281" class="Symbol">∀</a> <a id="11283" class="Symbol">{</a><a id="11284" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11284" class="Bound">A</a> <a id="11286" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11286" class="Bound">B</a> <a id="11288" class="Symbol">:</a> <a id="11290" class="PrimitiveType">Set</a><a id="11293" class="Symbol">}</a> <a id="11295" class="Symbol">→</a> <a id="11297" class="Symbol">(((</a><a id="11300" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11284" class="Bound">A</a> <a id="11302" class="Symbol">→</a> <a id="11304" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11286" class="Bound">B</a><a id="11305" class="Symbol">)</a> <a id="11307" class="Symbol">→</a> <a id="11309" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11284" class="Bound">A</a><a id="11310" class="Symbol">)</a> <a id="11312" class="Symbol">→</a> <a id="11314" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11284" class="Bound">A</a><a id="11315" class="Symbol">)</a>
<a id="11317" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11219" class="Function">Implication</a> <a id="11329" class="Symbol">=</a> <a id="11331" class="Symbol">∀</a> <a id="11333" class="Symbol">{</a><a id="11334" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11334" class="Bound">A</a> <a id="11336" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11336" class="Bound">B</a> <a id="11338" class="Symbol">:</a> <a id="11340" class="PrimitiveType">Set</a><a id="11343" class="Symbol">}</a> <a id="11345" class="Symbol">→</a> <a id="11347" class="Symbol">(</a><a id="11348" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11334" class="Bound">A</a> <a id="11350" class="Symbol">→</a> <a id="11352" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11336" class="Bound">B</a><a id="11353" class="Symbol">)</a> <a id="11355" class="Symbol">→</a> <a id="11357" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#789" class="Function Operator">¬</a> <a id="11359" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11334" class="Bound">A</a> <a id="11361" href="https://agda.github.io/agda-stdlib/Data.Sum.html#508" class="Datatype Operator">⊎</a> <a id="11363" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11336" class="Bound">B</a>
<a id="×-Implies-⊎"></a><a id="11365" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11365" class="Function">×-Implies-⊎</a> <a id="11377" class="Symbol">=</a> <a id="11379" class="Symbol">∀</a> <a id="11381" class="Symbol">{</a><a id="11382" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11382" class="Bound">A</a> <a id="11384" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11384" class="Bound">B</a> <a id="11386" class="Symbol">:</a> <a id="11388" class="PrimitiveType">Set</a><a id="11391" class="Symbol">}</a> <a id="11393" class="Symbol">→</a> <a id="11395" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#789" class="Function Operator">¬</a> <a id="11397" class="Symbol">(</a><a id="11398" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11382" class="Bound">A</a> <a id="11400" href="https://agda.github.io/agda-stdlib/Data.Product.html#1329" class="Function Operator">×</a> <a id="11402" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11384" class="Bound">B</a><a id="11403" class="Symbol">)</a> <a id="11405" class="Symbol">→</a> <a id="11407" class="Symbol">(</a><a id="11408" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#789" class="Function Operator">¬</a> <a id="11410" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11382" class="Bound">A</a><a id="11411" class="Symbol">)</a> <a id="11413" href="https://agda.github.io/agda-stdlib/Data.Sum.html#508" class="Datatype Operator">⊎</a> <a id="11415" class="Symbol">(</a><a id="11416" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#789" class="Function Operator">¬</a> <a id="11418" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11384" class="Bound">B</a><a id="11419" class="Symbol">)</a>{% endraw %}</pre>

    
### Exercise (`¬-stable`, `×-stable`)

Say that a formula is *stable* if double negation elimination holds for it.
<pre class="Agda">{% raw %}<a id="Stable"></a><a id="11566" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11566" class="Function">Stable</a> <a id="11573" class="Symbol">:</a> <a id="11575" class="PrimitiveType">Set</a> <a id="11579" class="Symbol">→</a> <a id="11581" class="PrimitiveType">Set</a>
<a id="11585" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11566" class="Function">Stable</a> <a id="11592" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11592" class="Bound">A</a> <a id="11594" class="Symbol">=</a> <a id="11596" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#789" class="Function Operator">¬</a> <a id="11598" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#789" class="Function Operator">¬</a> <a id="11600" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11592" class="Bound">A</a> <a id="11602" class="Symbol">→</a> <a id="11604" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11592" class="Bound">A</a>{% endraw %}</pre>
Show that any negated formula is stable, and that the conjunction
of two stable formulas is stable.
<pre class="Agda">{% raw %}<a id="11730" class="Keyword">postulate</a>
  <a id="¬-stable"></a><a id="11742" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11742" class="Postulate">¬-stable</a> <a id="11751" class="Symbol">:</a> <a id="11753" class="Symbol">∀</a> <a id="11755" class="Symbol">{</a><a id="11756" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11756" class="Bound">A</a> <a id="11758" class="Symbol">:</a> <a id="11760" class="PrimitiveType">Set</a><a id="11763" class="Symbol">}</a> <a id="11765" class="Symbol">→</a> <a id="11767" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11566" class="Function">Stable</a> <a id="11774" class="Symbol">(</a><a id="11775" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#789" class="Function Operator">¬</a> <a id="11777" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11756" class="Bound">A</a><a id="11778" class="Symbol">)</a>
  <a id="×-stable"></a><a id="11782" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11782" class="Postulate">×-stable</a> <a id="11791" class="Symbol">:</a> <a id="11793" class="Symbol">∀</a> <a id="11795" class="Symbol">{</a><a id="11796" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11796" class="Bound">A</a> <a id="11798" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11798" class="Bound">B</a> <a id="11800" class="Symbol">:</a> <a id="11802" class="PrimitiveType">Set</a><a id="11805" class="Symbol">}</a> <a id="11807" class="Symbol">→</a> <a id="11809" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11566" class="Function">Stable</a> <a id="11816" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11796" class="Bound">A</a> <a id="11818" class="Symbol">→</a> <a id="11820" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11566" class="Function">Stable</a> <a id="11827" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11798" class="Bound">B</a> <a id="11829" class="Symbol">→</a> <a id="11831" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11566" class="Function">Stable</a> <a id="11838" class="Symbol">(</a><a id="11839" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11796" class="Bound">A</a> <a id="11841" href="https://agda.github.io/agda-stdlib/Data.Product.html#1329" class="Function Operator">×</a> <a id="11843" href="{% endraw %}{{ site.baseurl }}{% link out/Negation.md %}{% raw %}#11798" class="Bound">B</a><a id="11844" class="Symbol">)</a>{% endraw %}</pre>

## Standard Prelude

Definitions similar to those in this chapter can be found in the standard library.
<pre class="Agda">{% raw %}<a id="11975" class="Keyword">import</a> <a id="11982" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="11999" class="Keyword">using</a> <a id="12005" class="Symbol">(</a><a id="12006" href="https://agda.github.io/agda-stdlib/Relation.Nullary.html#464" class="Function Operator">¬_</a><a id="12008" class="Symbol">)</a>
<a id="12010" class="Keyword">import</a> <a id="12017" href="https://agda.github.io/agda-stdlib/Relation.Nullary.Negation.html" class="Module">Relation.Nullary.Negation</a> <a id="12043" class="Keyword">using</a> <a id="12049" class="Symbol">(</a><a id="12050" href="https://agda.github.io/agda-stdlib/Relation.Nullary.Negation.html#657" class="Function">contraposition</a><a id="12064" class="Symbol">)</a>{% endraw %}</pre>

## Unicode

This chapter uses the following unicode.

    ¬  U+00AC  NOT SIGN (\neg)
