Todo
----

+ CREATE 00_Motivation_Bugs.lhs **TUFTS**
  + sequence, BUGs, 1984, etc.

+ UPDATE 11_Evaluation.lhs **TUFTS,BOS** 
  + Add bits about "comments" ---> "types"
  + Nicer GRAPHS
  
+ CREATE HARDWIRED-RED-BLACK-BST.lhs **TUFTS**
  + INV 1: COLOR
  + INV 2: HEIGHT
  + INV 3: ORDER

+ CREATE 03_Memory.lhs **TUFTS, BOS**
  + and associated demo file, from eseidel's BS demo.

+ UPDATE 09_Laziness.lhs **BOS**
  + Use math fonts
  
+ CHECK 10_Termination.lhs **BOS**
  + link to Termination.hs demo
  
Comparison with DT
------------------

-- Grisly HS+DT proof
https://github.com/jstolarek/dep-typed-wbl-heaps-hs/blob/master/src/TwoPassMerge/CombinedProofs.hs#L68

-- HS (no proof)
https://github.com/jstolarek/dep-typed-wbl-heaps-hs/blob/master/src/TwoPassMerge/NoProofs.hs#L96

-- HS+LH proof
https://github.com/ucsd-progsys/liquidhaskell/blob/master/tests/pos/WBL.hs#L129


BOS-Haskell Plan
----------------

[35] PART I "refinement types"

* [5]  00_Motivation: "Go Wrong"

* [15] 01_SimpleRefinements (upto VC, Abs) but no Kvar
    + Demo : hs/000_Refinements.hs
	+ Demo : hs/001_Refinements.hs
	
* [15] 02_Measures
    + Demo : hs/01_Elements.hs

[20] PART II "case studies"

* [5]  lhs/02_RedBlack.lhs	
* [15] lhs/13_Memory.lhs


[25] PART III "haskell"

* [10] lhs/09_Laziness.lhs
* [10] lhs/10_Termination.lhs
* [3]  lhs/11_Evaluation.lhs 
* [2]  lhs/12_Conclusion.lhs

[20] PART IV "abstract refinements"

* [5]  04_Abstract Refinements.lhs
    + Demo : 02_AbstractRefinements.hs (listMax)

* [7] Demo Inductive
    + Demo:  02_AbstractRefinements.hs (ifoldr, append, filter)
	  
* [8] Demo Recursive
	+ Demo:  02_AbstractRefinements.hs (insertSort, ifoldr-insertSort)
	+ Demo:  04_Streams.hs (repeat, take)

? [10] Demo Indexed
	+ Demo: KMP.hs

Tufts Plan
----------

* [7]  00_Motivation_Long
        + Bugs
		+ Well typed Program Go Wrong
		
* [10]  01_SimpleRefinements
        + upto VC, Abs

* [10] 02_Measures 
        + Demo    : 00_Refinements.hs
        + Demo    : 01_Elements.hs

* [5]  02_RedBlack 
		+ Complex : RED-BLACK Trees

* [5] 03_Memory_short?
		+ Upto just the low-level API?
		
* [5]  11_Evaluation.lhs 
		+ Add bits about "comments" ---> "types"
		
* [2]  12_Conclusion.lhs



Brown Plan
----------

* [5]  00_Motivation: "Go Wrong"

* [5]  01_SimpleRefinements (upto VC, Abs, but no Kvar)

* [10] 02_Measures [TODO: cut RED-BLACK]
    + Demo : 00_Refinements.hs
    + Demo : 01_Elements.hs

* [5]  04_Abstract Refinements
    + Demo : 02_AbstractRefinements.hs (listMax)
	
* [5]  06_Inductive
	+ Describe: [TODO: CUT ?foldn] foldr
    + Demo:  02_AbstractRefinements.hs (foldr, append, filter)

* [5]  08_Recursive
	+ Describe: list-ord
	+ Demo:  02_AbstractRefinements.hs (insertSort, ifoldr-insertSort)
	+ Show:  GhcListSort.hs 
	+ Describe: tree-ord
	+ Demo:     Stream
 
* [3]  11_Evaluation.lhs 

* [2]  12_Conclusion.lhs



Harvard Plan
------------

* [5] 00_Motivation: "Go Wrong"

* [5] 01_SimpleRefinements (upto VC, Abs, but no Kvar)

* [10] 02_Measures [TODO: cut RED-BLACK]
    + Demo : 00_Refinements.hs (upto "wtAverage")
    + Demo : 01_Elements.hs

* [5] 04_Abstract Refinements
    + Demo : 02_AbstractRefinements.hs (listMax)
	
* [5] 06_Inductive
	+ Describe: [TODO: CUT ?foldn] foldr
    + Demo:  02_AbstractRefinements.hs (foldr, append, filter)

* [5] 08_Recursive
	+ Describe: list-ord
	+ Demo:  02_AbstractRefinements.hs (insertSort, ifoldr-insertSort)

	+ Show:  GhcListSort.hs 
	+ Describe: tree-ord
	+ [TODO: CUT] Demo:     RBTree-Ord
	+ Demo:     Stream

* [TODO: CUT] [5] 07_Array
  [TODO: CUT] 	+ Describe: Array
  [TODO: CUT] 	+ Demo:     KMP
  
* [3] 11_Evaluation.lhs 

* [2] 12_Conclusion.lhs

Bytestring Details
------------------

-- | A variety of 'head' for non-empty ByteStrings. 'unsafeHead' omits
-- the check for the empty case, which is good for performance, but
-- there is an obligation on the programmer to provide a proof that the
-- ByteString is non-empty.
{-@ unsafeHead :: ByteStringNE -> Char @-}
unsafeHead :: ByteString -> Char
unsafeHead  = w2c . B.unsafeHead
{-# INLINE unsafeHead #-}


type ByteStringNE = {v:ByteString | 0 < bLength v}


-- | Unsafe 'ByteString' index (subscript) operator, starting from 0, returning a 'Word8'
-- This omits the bounds check, which means there is an accompanying
-- obligation on the programmer to ensure the bounds are checked in some
-- other way.

{-@ type OkIdx B = {v:Nat | v < bLength B} @-}

{-@ unsafeIndex :: b:ByteString -> OkIdx b -> Word8 @-}
unsafeIndex :: ByteString -> Int -> Word8
unsafeIndex (PS x s l) i = assert (i >= 0 && i < l) $
    inlinePerformIO $ withForeignPtr x $ \p -> peekByteOff p (s+i)


Low-Level Memory
----------------

1. "Haskell HeartBleed" (using BS)

2. Memory API (calls out to C)
	+ mallocForeignPtrBytes
	+ withForeignPtr 
	+ peek
	+ poke
	+ plusPtr

   First with types, then with Refined Types.

3. Examples
    + okPtr
	+ badPtr (replace 3 with 6)

4. `ByteString`
   + invariant 
   + goodBS1, goodBS2
   + badBS1, badBS2

5. `create`
   + good call
   + bad call
   
6. `pack`
7. `unpack`
8. `unsafeTake`
9. `heartBleed` redux.

`peekByteOff p i == peek (p `plusPtr` i)`

\begin{code}
module BSCrash where

import Data.ByteString.Char8  as C
import Data.ByteString        as B
import Data.ByteString.Unsafe as U

heartBleed s n = s'
  where 
    b          = C.pack s         -- "Ranjit"
    b'         = U.unsafeTake n b -- 20
    s'         = C.unpack b'

-- > let ex = "Ranjit Loves Burritos"
    
-- > heartBleed ex 1
--   "R"
    
-- > heartBleed ex 6
-- > "Ranjit"

-- > heartBleed ex 10
-- > "Ranjit Lov"
    
-- > heartBleed ex 30
-- > "Ranjit Loves Burritos\NUL\NUL\NUL\201\&1j\DC3\SOH\NUL"
\end{code}
