 {#measures}
============

Recap
-----

<br>
<br>

1. <div class="fragment">**Refinements:** Types + Predicates</div>
2. <div class="fragment">**Subtyping:** SMT Implication</div>

<br>
<br>

<div class="fragment">
So far: only specify properties of **base values** (e.g. `Int`) ...
</div>

<br>

<div class="fragment">
How to specify properties of **structures**?
</div>


<div class="hidden">

\begin{code}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--diff"           @-}

module Measures where
import Prelude hiding ((!!), length)
import Language.Haskell.Liquid.Prelude
\end{code}

</div>


 {#meas}
====================

Measuring Data Types
--------------------

Measuring Data Types
====================


Example: Length of a List
-------------------------

Given a type for lists:

<br>

\begin{spec}
data List a = [] | a : List a
\end{spec}

<div class="fragment">
<br>

We can define the **length** as:

<br>

\begin{spec}
{-@ measure size @-}
len        :: List a -> Int
len []     = 0
len (x:xs) = 1 + len xs
\end{spec}

</div>

<div class="hidden">
\begin{code}
type List a = [a]
\end{code}

</div>

Example: Length of a List
-------------------------

<br>

**Lists of size `N`**

<br>

\begin{code}
{-@ type ListN a N = {v:List a | len v == N} @-}
\end{code}


Example: Length of a List
-------------------------

<br>

**Lists of size equal to another list `X`**

<br>

\begin{code}
{-@ type ListX a X = ListN a (len X) @-}
\end{code}

Example: Length of a List
-------------------------

<br>

LiquidHaskell **strengthens** data constructor types

<br>

\begin{spec} <div/>
data List a where
  []  :: ListN a 0
  (:) :: a -> t:List a -> ListN a (1 + len t)
\end{spec}

<br>

Verification kept **decidable** [[PLDI 09]](http://fixme.com) [[ICFP 14]](http://fixme.com)


[[Example: Matrices]](15_Matrix.lhs.slides.html)
-----------------------

<br>
<br>
<br>




Multiple Measures
=================

 {#adasd}
---------

Can support *many* measures for a type


Ex: List Emptiness
------------------

<br>

Measure describing whether a `List` is empty

<br>

\begin{code}
{-@ measure isNull @-}
isNull []    = True
isNull (_:_) = False
\end{code}

<br>

Conjoin Multiple Refinements
----------------------------

<br>

\begin{spec}
data L a where
  []  :: {v:List a |  len v == 0
                   && isNull v  }
  (:) :: a
      -> xs:List a
      -> {v:List a |  len v = 1 + len xs
                   && not (isNull v)    }
\end{spec}



[[Example: Red-Black Trees]](13_RedBlack.lhs.slides.html)
-----------------------

<br>
<br>
<br>

Recap
-----

<br>
<br>


1. Refinements: Types + Predicates
2. Subtyping: SMT Implication
3. **Measures:** Strengthened Constructors

<br>

<div class="fragment">Automatic Verification of Data Structures</div>

<br>
<br>
