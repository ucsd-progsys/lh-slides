Abstract Refinements {#data}
============================

Recap
-----

**So far**

Abstract Invariants from Functions

<br>

<div class="fragment">

**Next**

Decouple invariants from **recursive** data structures
</div>



Decouple Invariants From Data {#recursive} 
==========================================

 {#asd}
-------

Recursive Structures 
--------------------

Lets see another example of decoupling...

<div class="hidden">
\begin{code}
{-# LANGUAGE NoMonomorphismRestriction #-}

module List (insertSort) where

{-@ LIQUID "--no-termination" @-}

mergeSort     :: Ord a => [a] -> [a]
insertSort :: (Ord a) => [a] -> L a 
slist :: L Int
slist' :: L Int
iGoUp, iGoDn, iDiff :: [Int]
infixr `C`
\end{code}
</div>

Decouple Invariants From Recursive Data
=======================================

Recall: Lists
-------------

\begin{code}
data L a = N 
         | C { hd :: a, tl :: L a }
\end{code}


Recall: Refined Constructors 
----------------------------

Define **increasing** Lists with *strengthened constructors*:

\begin{spec} <br>
data L a where
  N :: L a
  C :: hd:a -> tl: L {v:a | hd <= v} -> L a
\end{spec}

Problem: Decreasing Lists?
--------------------------

What if we need *both* [increasing *and* decreasing lists?](http://hackage.haskell.org/package/base-4.7.0.0/docs/src/Data-List.html#sort)

<br>

<div class="hidden">
[Separate (indexed) types](http://web.cecs.pdx.edu/~sheard/Code/QSort.html) get quite complicated ...
</div>

Abstract That Refinement!
-------------------------

\begin{code}
{-@ data L a <p :: a -> a -> Prop>
      = N 
      | C { hd :: a, tl :: L <p> a<p hd> } @-}
\end{code}

<br>

<div class="fragment"> `p` is a **binary relation** between two `a` values</div>

<br>

<div class="fragment"> Definition relates `hd` with **all** the elements of `tl`</div>

<br>

<div class="fragment"> Recursive: `p` holds for **every pair** of elements!</div>

Example
-------

Consider a list with *three* or more elements 

\begin{spec} <br>
x1 `C` x2 `C` x3 `C` rest :: L <p> a 
\end{spec}

Example: Unfold Once
--------------------

\begin{spec} <br> 
x1                 :: a
x2 `C` x3 `C` rest :: L <p> a<p x1> 
\end{spec}

Example: Unfold Twice
---------------------

\begin{spec} <br> 
x1          :: a
x2          :: a<p x1>  
x3 `C` rest :: L <p> a<p x1 && p x2> 
\end{spec}

Example: Unfold Thrice
----------------------

\begin{spec} <br> 
x1   :: a
x2   :: a<p x1>  
x3   :: a<p x1 && p x2>  
rest :: L <p> a<p x1 && p x2 && p x3> 
\end{spec}

<br>

<div class="fragment">
Note how `p` holds between **every pair** of elements in the list. 
</div>

A Concrete Example
------------------

That was a rather *abstract*!

<br>

How can we *use* fact that `p` holds between *every pair*?

<br>

<div class="fragment">**Instantiate** `p` with a *concrete* refinement</div>



Example: Increasing Lists
-------------------------

**Instantiate** `p` with a *concrete* refinement

<br>

\begin{code}
{-@ type IncL a = L <{\hd v -> hd <= v}> a @-}
\end{code}

<br>

<div class="fragment"> Refinement says: &nbsp; `hd` less than **every** `v` in tail,</div>

<br>

<div class="fragment"> i.e., `IncL` denotes **increasing** lists. </div>

<br>

<div class="fragment"> [DEMO 02_AbstractRefinements.hs #3](02_AbstractRefinements.hs) </div>

<!-- BEGIN CUT 

Example: Increasing Lists
-------------------------

LiquidHaskell *verifies* that `slist` is indeed increasing...

\begin{code}
{-@ slist :: IncL Int @-}
slist     = 1 `C` 6 `C` 12 `C` N
\end{code}

<br> 

<div class="fragment">

... and *protests* that `slist'` is not: 

\begin{code}
{-@ slist' :: IncL Int @-}
slist' = 6 `C` 1 `C` 12 `C` N
\end{code}
</div>

Insertion Sort
--------------

\begin{code}
{-@ insertSort :: (Ord a) => [a] -> IncL a @-}
insertSort     = foldr insert N

insert y N          = y `C` N
insert y (x `C` xs) 
  | y < x           = y `C` (x `C` xs)
  | otherwise       = x `C` insert y xs
\end{code}

<br>

(Mouseover `insert` to see inferred type.)

Checking GHC Lists
------------------

<a href="http://goto.ucsd.edu:8090/index.html#?demo=Order.hs" target= "_blank">Demo:</a> 
Above applies to GHC's List definition:

\begin{spec} <br> 
data [a] <p :: a -> a -> Prop>
  = [] 
  | (:) { h :: a, tl :: [a<p h>]<p> }
\end{spec}

Checking GHC Lists
------------------

Increasing Lists

<br>

\begin{code}
{-@ type Incs a = [a]<{\h v -> h <= v}> @-}

{-@ iGoUp :: Incs Int @-}
iGoUp     = [1,2,3]
\end{code}

Checking GHC Lists
------------------

Decreasing Lists

<br>

\begin{code}
{-@ type Decs a = [a]<{\h v -> h >= v}> @-}

{-@ iGoDn :: Decs Int @-}
iGoDn     = [3,2,1]
\end{code}


Checking GHC Lists
------------------

Duplicate-free Lists

<br>

\begin{code}
{-@ type Difs a = [a]<{\h v -> h /= v}> @-}

{-@ iDiff :: Difs Int @-}
iDiff     = [1,3,2]
\end{code}

END CUT -->

Example: Sorting Lists
----------------------

Now we can check all the usual list sorting algorithms 

<br>

<a href="http://goto.ucsd.edu:8090/index.html#?demo=Order.hs" target="_blank">Demo:</a> List Sorting

<br>
<br>

[DEMO GhcListSort.hs](../hs/GhcListSort.hs)

<!-- BEGIN CUT 

Example: `mergeSort` [1/2]
--------------------------

\begin{code}
{-@ mergeSort  :: (Ord a) => [a] -> Incs a @-}
mergeSort []   = []
mergeSort [x]  = [x]
mergeSort xs   = merge xs1' xs2' 
  where 
   (xs1, xs2)  = split xs
   xs1'        = mergeSort xs1
   xs2'        = mergeSort xs2
\end{code}

Example: `mergeSort` [2/2]
--------------------------

\begin{code}
split (x:y:zs) = (x:xs, y:ys) 
  where 
    (xs, ys)   = split zs
split xs       = (xs, [])

merge xs []    = xs
merge [] ys    = ys
merge (x:xs) (y:ys) 
  | x <= y     = x : merge xs (y:ys)
  | otherwise  = y : merge (x:xs) ys
\end{code}

END CUT -->

Example: Binary Trees
---------------------

`Map` from keys of type `k` to values of type `a` 

<br>

<div class="fragment">

Implemented, as a binary tree:

<br>

\begin{code}
data Map k a = Tip
             | Bin Int k a (Map k a) (Map k a)
\end{code}
</div>

Two Abstract Refinements
------------------------

- `l` : relates root `key` with `left`-subtree keys
- `r` : relates root `key` with `right`-subtree keys

<br>

\begin{code}
{-@ data Map k a < l :: k -> k -> Prop
                 , r :: k -> k -> Prop >
    = Tip
    | Bin { sz    :: Int
          , key   :: k
          , val   :: a
          , left  :: Map <l,r> k<l key> a
          , right :: Map <l,r> k<r key> a} @-}
\end{code}


Ex: Binary Search Trees
-----------------------

Keys are *Binary-Search* Ordered

<br>

\begin{code}
{-@ type BST k a = 
      Map <{\r v -> v < r }, 
           {\r v -> v > r }> 
          k a                   @-}
\end{code}

Ex: Minimum Heaps 
-----------------

Root contains *minimum* value

<br>

\begin{code}
{-@ type MinHeap k a = 
      Map <{\r v -> r <= v}, 
           {\r v -> r <= v}> 
           k a               @-}
\end{code}

Ex: Maximum Heaps 
-----------------

Root contains *maximum* value

<br>

\begin{code}
{-@ type MaxHeap k a = 
      Map <{\r v -> r >= v}, 
           {\r v -> r >= v}> 
           k a               @-}
\end{code}


Example: Data.Map
-----------------

Standard Key-Value container

<br>

- <div class="fragment">1300+ non-comment lines</div>

- <div class="fragment">`insert`, `split`, `merge`,...</div>

- <div class="fragment">Rotation, Rebalance,...</div>

<br>

<div class="fragment">
SMT & inference crucial for [verification](https://github.com/ucsd-progsys/liquidhaskell/blob/master/benchmarks/esop2013-submission/Base.hs)
</div>

<br>

<div class="fragment">
<a href="http://goto.ucsd.edu:8090/index.html#?demo=Map.hs" target="_blank">Demo:</a> Binary Search Maps
</div>

Example: Red-Black Tree 
-----------------------

<br>

Binary-Search Ordered Keys

<br>

[DEMO RBTree-Ord.hs](../hs/RBTree-ord.hs)
Example: Infinite Streams 
-------------------------

<br>

How to distinguish between **finite** and **infinite** lists?

<br>

[DEMO Streams.hs](../hs/Streams.hs)


Recap: Abstract Refinements
---------------------------

<div class="fragment">

Decouple invariants from **functions**

+ `max`
+ `foldr`

</div>

<br>

<div class="fragment">
Decouple invariants from **data**

+ `List`
+ `Tree`

</div>


Recap
-----

1. Refinements: Types + Predicates
2. Subtyping: SMT Implication
3. Measures: Strengthened Constructors
4. Abstract Refinements over Functions
5. **Abstract** Refinements over Recursive Data
6. <div class="fragment">[Evaluation](11_Evaluation.lhs.slides.html)</div>
<br>
<br>

<div class="fragment">[[continue...]](11_Evaluation.lhs.slides.html)</div>
