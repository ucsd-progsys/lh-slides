 {#measures}
============

<div class="hidden">

\begin{code}
{-@ LIQUID "--no-termination" @-}

module Matrix (matProd, dotProduct, matProduct) where
import Prelude hiding ((!!), length)
import Language.Haskell.Liquid.Prelude

{-@ deadCode :: {v:String | false} -> a @-}
deadCode msg = error msg

type Vector a = [a]

data Matrix a = M { rows  :: Int
                  , cols  :: Int
                  , mElts :: Vector (Vector a)
                  }

transpose :: Matrix a -> Matrix a
transpose (M r c rows) = undefined

\end{code}

</div>


Vectors
-------

\begin{code}
{-@ type Vector a = [a] @-}

-- | Vectors of size N
{-@ type VectorN a N = {v:Vector a | len v == N} @-}

-- | Vectors of Size Equal to Another Vector X
{-@ type VectorX a X = VectorN a (len X)        @-}
\end{code}

Dot Product
-----------

\begin{code}
{-@ dotProduct :: (Num a) => vx:Vector a -> vy:VectorX a vx -> a @-}
dotProduct (x:xs) (y:ys) = (x * y) + dotProduct xs ys
dotProduct []     []     = 0
dotProduct _      _      = deadCode "dimension mismatch!"
\end{code}

Transforming Vectors
--------------------

\begin{code}
{-@ forEach :: x:Vector a -> (a -> b) -> VectorX b x @-}
forEach []     _ = []
forEach (x:xs) f = f x : forEach xs f
\end{code}


Matrices
--------

\begin{code}
{-@ data Matrix a =
      M { rows  :: Nat
        , cols  :: Nat
        , mElts :: VectorN (VectorN a cols) rows
        }
  @-}
\end{code}

Matrix Dimensions
-----------------

\begin{code}
{-@ type MatrixR  a R   = {v:Matrix a    | rows v == R} @-}
{-@ type MatrixRC a R C = {v:MatrixR a R | cols v == C} @-}
\end{code}

Matrix Product (Buggy)
----------------------

\begin{code}
matProd :: (Num a) => Matrix a -> Matrix a -> Matrix a
matProd (M rx _ xs) my@(M _ cy ys)
                 = M rx cy elts
  where
    elts         = forEach xs (\xi ->
                     forEach ys (\yj ->
                       dotProduct xi yj
                     )
                   )
\end{code}

Matrix Product (Fixed)
----------------------

\begin{code}
{-@ matProduct :: (Num a) => x:Matrix a
                          -> y:MatrixR a  (cols x)
                          ->   MatrixRC a (rows x) (cols y)
  @-}
matProduct (M rx _ xs) my@(M _ cy _)
                 = M rx cy elts
  where
    elts         = forEach xs (\xi ->
                     forEach ys (\yj ->
                       dotProduct xi yj
                     )
                   )
    M _ _ ys     = transpose my
\end{code}

where

\begin{code}
{-@ transpose :: m:Matrix a -> MatrixRC a (cols m) (rows m) @-}
\end{code}



