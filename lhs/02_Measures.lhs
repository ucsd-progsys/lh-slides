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

\begin{spec}
{-@ measure size @-}
len        :: List a -> Int
len []     = 0
len (x:xs) = 1 + len xs
\end{spec}

<br>

We **strengthen** data constructor types

<br>

\begin{spec} <div/>
data List a where
  []  :: {v:List a | len v == 0}
  (:) :: a -> t:List a -> {v:List a| len v = 1 + len t}
\end{spec}

Example: Using Measures
-----------------------

<br>
<br>

[DEMO: Vectors and Matrices](15_Matrix.lhs)


Multiple Measures
=================

 {#adasd}
---------

Can support *many* measures for a type


Ex: List Emptiness
------------------

Measure describing whether a `List` is empty

\begin{code}
{-@ measure isNull @-}
isNull []    = True
isNull (_:_) = False
\end{code}

<br>

<div class="fragment">
LiquidHaskell **strengthens** data constructors

\begin{spec}
data List a where
  []  :: {v : List a | isNull v}
  (:) :: a -> List a -> {v:List a | not (isNull v)}
\end{spec}

</div>

Conjoining Refinements
----------------------

Data constructor refinements are **conjoined**

\begin{spec}
data L a where
  []  :: {v:List a |  len v == 0
                 && isNull v  }
  (:) :: a
      -> xs:List a
      -> {v:List a |  len v = 1 + len xs
                   && not (isNull v)    }
\end{spec}


Multiple Measures: Red Black Trees
==================================

 {#elements}
------------

<br>
<br>
<br>

<a href="13_RedBlack.lhs.slides.html" target="_blank">[continue]</a>

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
