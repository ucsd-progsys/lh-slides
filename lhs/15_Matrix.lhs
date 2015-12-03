 {#measures}
============

<div class="hidden">

\begin{code}
{-@ LIQUID "--no-termination" @-}

module Mat (matProd', dotProd, matProd) where
import Prelude hiding ((!!), length)
import Language.Haskell.Liquid.Prelude

{-@ deadCode :: {v:String | false} -> a @-}
deadCode msg = error msg

type Vec a = [a]

data Mat a = M { rows  :: Int
               , cols  :: Int
               , mElts :: Vec (Vec a)
               }

{-@ rows :: m:Mat a -> {v:Int | v == rows m } @-}
{-@ cols :: m:Mat a -> {v:Int | v == cols m } @-}

{-@ txPose :: m:Mat a -> MatRC a (cols m) (rows m) @-}
txPose :: Mat a -> Mat a
txPose = undefined


{-@ type MatR a R    = {v:Mat a    | rows v = R}  @-}
{-@ type MatRC a R C = {v:MatR a R | cols v == C} @-}
\end{code}

</div>


Vectors
-------

<br>

Lets implement vectors using lists

<br>

\begin{code}
{-@ type Vec a = [a] @-}
\end{code}

Vector Dimensions
-----------------

<br>

<div class="fragment">
**Vectors of dimension `N`**

<br>

\begin{code}
{-@ type VecN a N = {v:Vec a | len v == N} @-}
\end{code}
</div>

<br>

<div class="fragment">
**Vectors of equal dimension**

<br>

\begin{code}
{-@ type VecX a X = VecN a (len X)        @-}
\end{code}
</div>

Dot Product
-----------


<br>

**Compute Dot-Product of Vectors**

<br>


\begin{code}
{-@ dotProd :: (Num a)
            => x:Vec a -> y:VecX a x -> a
  @-}
dotProd (x:xs) (y:ys) = (x * y) + dotProd xs ys
dotProd []     []     = 0
dotProd _      _      = deadCode "dim mismatch!"
\end{code}

Transforming Vectors
--------------------

<br>

**Transform each element of a vector**

<br>

\begin{code}
{-@ forEach :: x:Vec a -> (a -> b) -> VecX b x
  @-}
forEach []     _ = []
forEach (x:xs) f = f x : forEach xs f
\end{code}


Matrices
--------

<br>

**A matrix is a vector of vectors**

<br>

\begin{code}
{-@ data Mat a =
      M { rows  :: Nat
        , cols  :: Nat
        , mElts :: VecN (VecN a cols) rows
        }
  @-}
\end{code}

Matrix Dimensions
-----------------

<br>


<div class="fragment">
**Matrices with a given number of rows**

<br>

\begin{spec}
type MatR a R = {v:Mat a | rows v == R}
\end{spec}

</div>

<br>

<div class="fragment">
**Matrices with a given number of rows and columns**

<br>

\begin{spec}
type MatRC a R C = {v:MatR a R | cols v == C}
\end{spec}
</div>

Matrix Product (Buggy)
----------------------

What's wrong with this code?

<br>

\begin{code}
matProd' :: (Num a) => Mat a -> Mat a -> Mat a
matProd' (M rx _ xs) my@(M _ cy ys)
                 = M rx cy elts
  where
    elts         = forEach xs (\xi ->
                     forEach ys (\yj ->
                       dotProd xi yj
                     )
                   )
\end{code}

<br>

<div class="fragment">
Oops! Only multiply **compatible** matrices!
</div>

Matrix Product (Fixed)
----------------------

<br>

**Specify:** Input and Output Dimensions

<br>

\begin{code}
{-@ matProd :: (Num a)
            => x:Mat a
            -> y:MatR a (cols x)
            -> MatRC a (rows x) (cols y)
  @-}
\end{code}

Matrix Product (Fixed)
----------------------

**Verify**

\begin{code}
matProd (M rx _ xs) my@(M _ cy _)
             = M rx cy elts
  where
    elts     = forEach xs $ \xi ->
                 forEach ys $ \yj ->
                   dotProd xi yj
    M _ _ ys = txPose my
\end{code}

<br>

<div class="fragment">
where
\begin{spec}
txPose :: m:Mat a -> MatRC a (cols m) (rows m)
\end{spec}

</div>


[[continue]](02_Measures.lhs.slides.html#/adasd)
------------------------------------------------
