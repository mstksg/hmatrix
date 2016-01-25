{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}


{- |
Module      :  Numeric.LinearAlgebra.Static
Copyright   :  (c) Alberto Ruiz 2014
License     :  BSD3
Stability   :  experimental

Experimental interface with statically checked dimensions.

See code examples at http://dis.um.es/~alberto/hmatrix/static.html.

-}

module Numeric.LinearAlgebra.Static(
    -- * Vector
       ℝ, R,
    vec2, vec3, vec4, (&), (#), split, headTail,
    vector,
    linspace, range, dim,
    -- * Matrix
    L, Sq, build,
    row, col, (|||),(===), splitRows, splitCols,
    unrow, uncol,
    tr,
    eye,
    diag,
    blockAt,
    matrix,
    -- * Complex
    C, M, Her, her, 𝑖,
    -- * Products
    (<>),(#>),(<.>),
    -- * Linear Systems
    linSolve, (<\>),
    -- * Factorizations
    svd, withCompactSVD, svdTall, svdFlat, Eigen(..),
    withNullspace, withOrth, qr, chol,
    -- * Norms
    Normed(..),
    -- * Random arrays
    Seed, RandDist(..),
    randomVector, rand, randn, gaussianSample, uniformSample,
    -- * Misc
    mean, meanCov,
    Disp(..), Domain(..),
    withVector, withMatrix, exactLength, exactDims,
    toRows, toColumns, withRows, withColumns,
    Sized(..), Diag(..), Sym, sym, mTm, unSym, (<·>)
) where


import GHC.TypeLits
import Numeric.LinearAlgebra hiding (
    (<>),(#>),(<.>),Konst(..),diag, disp,(===),(|||),
    row,col,vector,matrix,linspace,toRows,toColumns,
    (<\>),fromList,takeDiag,svd,eig,eigSH,
    eigenvalues,eigenvaluesSH,build,
    qr,size,dot,chol,range,R,C,sym,mTm,unSym,
    randomVector,rand,randn,gaussianSample,uniformSample,meanCov)
import qualified Numeric.LinearAlgebra as LA
import qualified Numeric.LinearAlgebra.Devel as LA
import Data.Proxy(Proxy(..))
import Internal.Static
import Control.Arrow((***))
import Text.Printf
import Data.Type.Equality ((:~:)(..))

ud1 :: R n -> Vector ℝ
ud1 (R (Dim v)) = v


infixl 4 &
(&) :: forall n . (KnownNat n, 1 <= n)
    => R n -> ℝ -> R (n+1)
u & x = u # (konst x :: R 1)

infixl 4 #
(#) :: forall n m . (KnownNat n, KnownNat m)
    => R n -> R m -> R (n+m)
(R u) # (R v) = R (vconcat u v)



vec2 :: ℝ -> ℝ -> R 2
vec2 a b = R (gvec2 a b)

vec3 :: ℝ -> ℝ -> ℝ -> R 3
vec3 a b c = R (gvec3 a b c)


vec4 :: ℝ -> ℝ -> ℝ -> ℝ -> R 4
vec4 a b c d = R (gvec4 a b c d)

vector :: KnownNat n => [ℝ] -> R n
vector = fromList

matrix :: (KnownNat m, KnownNat n) => [ℝ] -> L m n
matrix = fromList

linspace :: forall n . KnownNat n => (ℝ,ℝ) -> R n
linspace (a,b) = v
  where
    v = mkR (LA.linspace (size v) (a,b))

range :: forall n . KnownNat n => R n
range = v
  where
    v = mkR (LA.linspace d (1,fromIntegral d))
    d = size v

dim :: forall n . KnownNat n => R n
dim = v
  where
    v = mkR (scalar (fromIntegral $ size v))

--------------------------------------------------------------------------------


ud2 :: L m n -> Matrix ℝ
ud2 (L (Dim (Dim x))) = x


--------------------------------------------------------------------------------

diag :: KnownNat n => R n -> Sq n
diag = diagR 0

eye :: KnownNat n => Sq n
eye = diag 1

--------------------------------------------------------------------------------

blockAt :: forall m n . (KnownNat m, KnownNat n) =>  ℝ -> Int -> Int -> Matrix Double -> L m n
blockAt x r c a = res
  where
    z = scalar x
    z1 = LA.konst x (r,c)
    z2 = LA.konst x (max 0 (m'-(ra+r)), max 0 (n'-(ca+c)))
    ra = min (rows a) . max 0 $ m'-r
    ca = min (cols a) . max 0 $ n'-c
    sa = subMatrix (0,0) (ra, ca) a
    (m',n') = size res
    res = mkL $ fromBlocks [[z1,z,z],[z,sa,z],[z,z,z2]]

--------------------------------------------------------------------------------


row :: R n -> L 1 n
row = mkL . asRow . ud1

--col :: R n -> L n 1
col v = tr . row $ v

unrow :: L 1 n -> R n
unrow = mkR . head . LA.toRows . ud2

--uncol :: L n 1 -> R n
uncol v = unrow . tr $ v


infixl 2 ===
(===) :: (KnownNat r1, KnownNat r2, KnownNat c) => L r1 c -> L r2 c -> L (r1+r2) c
a === b = mkL (extract a LA.=== extract b)


infixl 3 |||
-- (|||) :: (KnownNat r, KnownNat c1, KnownNat c2) => L r c1 -> L r c2 -> L r (c1+c2)
a ||| b = tr (tr a === tr b)


type Sq n  = L n n
--type CSq n = CL n n


type GL = forall n m . (KnownNat n, KnownNat m) => L m n
type GSq = forall n . KnownNat n => Sq n

isKonst :: forall m n . (KnownNat m, KnownNat n) => L m n -> Maybe (ℝ,(Int,Int))
isKonst s@(unwrap -> x)
    | singleM x = Just (x `atIndex` (0,0), (size s))
    | otherwise = Nothing


isKonstC :: forall m n . (KnownNat m, KnownNat n) => M m n -> Maybe (ℂ,(Int,Int))
isKonstC s@(unwrap -> x)
    | singleM x = Just (x `atIndex` (0,0), (size s))
    | otherwise = Nothing


infixr 8 <>
(<>) :: forall m k n. (KnownNat m, KnownNat k, KnownNat n) => L m k -> L k n -> L m n
(<>) = mulR


infixr 8 #>
(#>) :: (KnownNat m, KnownNat n) => L m n -> R n -> R m
(#>) = appR


infixr 8 <·>
(<·>) :: R n -> R n -> ℝ
(<·>) = dotR

infixr 8 <.>
(<.>) :: R n -> R n -> ℝ
(<.>) = dotR

--------------------------------------------------------------------------------

class Diag m d | m -> d
  where
    takeDiag :: m -> d


instance KnownNat n => Diag (L n n) (R n)
  where
    takeDiag x = mkR (LA.takeDiag (extract x))


instance KnownNat n => Diag (M n n) (C n)
  where
    takeDiag x = mkC (LA.takeDiag (extract x))


--------------------------------------------------------------------------------

linSolve :: (KnownNat m, KnownNat n) => L m m -> L m n -> Maybe (L m n)
linSolve (extract -> a) (extract -> b) = fmap mkL (LA.linearSolve a b)

(<\>) :: (KnownNat m, KnownNat n, KnownNat r) => L m n -> L m r -> L n r
(extract -> a) <\> (extract -> b) = mkL (a LA.<\> b)

svd :: (KnownNat m, KnownNat n) => L m n -> (L m m, R n, L n n)
svd (extract -> m) = (mkL u, mkR s', mkL v)
  where
    (u,s,v) = LA.svd m
    s' = vjoin [s, z]
    z = LA.konst 0 (max 0 (cols m - LA.size s))


svdTall :: (KnownNat m, KnownNat n, n <= m) => L m n -> (L m n, R n, L n n)
svdTall (extract -> m) = (mkL u, mkR s, mkL v)
  where
    (u,s,v) = LA.thinSVD m


svdFlat :: (KnownNat m, KnownNat n, m <= n) => L m n -> (L m m, R m, L n m)
svdFlat (extract -> m) = (mkL u, mkR s, mkL v)
  where
    (u,s,v) = LA.thinSVD m

--------------------------------------------------------------------------------

class Eigen m l v | m -> l, m -> v
  where
    eigensystem :: m -> (l,v)
    eigenvalues :: m -> l

newtype Sym n = Sym (Sq n) deriving Show


sym :: KnownNat n => Sq n -> Sym n
sym m = Sym $ (m + tr m)/2

mTm :: (KnownNat m, KnownNat n) => L m n -> Sym n
mTm x = Sym (tr x <> x)

unSym :: Sym n -> Sq n
unSym (Sym x) = x


𝑖 :: Sized ℂ s c => s
𝑖 = konst iC

newtype Her n = Her (M n n)

her :: KnownNat n => M n n -> Her n
her m = Her $ (m + LA.tr m)/2


instance (KnownNat n) => Disp (Sym n)
  where
    disp n (Sym x) = do
        let a = extract x
        let su = LA.dispf n a
        printf "Sym %d" (cols a) >> putStr (dropWhile (/='\n') $ su)

instance (KnownNat n) => Disp (Her n)
  where
    disp n (Her x) = do
        let a = extract x
        let su = LA.dispcf n a
        printf "Her %d" (cols a) >> putStr (dropWhile (/='\n') $ su)


instance KnownNat n => Eigen (Sym n) (R n) (L n n)
  where
    eigenvalues (Sym (extract -> m)) =  mkR . LA.eigenvaluesSH . LA.trustSym $ m
    eigensystem (Sym (extract -> m)) = (mkR l, mkL v)
      where
        (l,v) = LA.eigSH . LA.trustSym $ m

instance KnownNat n => Eigen (Sq n) (C n) (M n n)
  where
    eigenvalues (extract -> m) = mkC . LA.eigenvalues $ m
    eigensystem (extract -> m) = (mkC l, mkM v)
      where
        (l,v) = LA.eig m

chol :: KnownNat n => Sym n -> Sq n
chol (extract . unSym -> m) = mkL $ LA.chol $ LA.trustSym m

--------------------------------------------------------------------------------

withNullspace
    :: forall m n z . (KnownNat m, KnownNat n)
    => L m n
    -> (forall k . (KnownNat k) => L n k -> z)
    -> z
withNullspace (LA.nullspace . extract -> a) f =
    case someNatVal $ fromIntegral $ cols a of
       Nothing -> error "static/dynamic mismatch"
       Just (SomeNat (_ :: Proxy k)) -> f (mkL a :: L n k)

withOrth
    :: forall m n z . (KnownNat m, KnownNat n)
    => L m n
    -> (forall k. (KnownNat k) => L n k -> z)
    -> z
withOrth (LA.orth . extract -> a) f =
    case someNatVal $ fromIntegral $ cols a of
       Nothing -> error "static/dynamic mismatch"
       Just (SomeNat (_ :: Proxy k)) -> f (mkL a :: L n k)

withCompactSVD
    :: forall m n z . (KnownNat m, KnownNat n)
    => L m n
    -> (forall k . (KnownNat k) => (L m k, R k, L n k) -> z)
    -> z
withCompactSVD (LA.compactSVD . extract -> (u,s,v)) f =
    case someNatVal $ fromIntegral $ LA.size s of
       Nothing -> error "static/dynamic mismatch"
       Just (SomeNat (_ :: Proxy k)) -> f (mkL u :: L m k, mkR s :: R k, mkL v :: L n k)

--------------------------------------------------------------------------------

qr :: (KnownNat m, KnownNat n) => L m n -> (L m m, L m n)
qr (extract -> x) = (mkL q, mkL r)
  where
    (q,r) = LA.qr x

-- use qrRaw?

--------------------------------------------------------------------------------

split :: forall p n . (KnownNat p, KnownNat n, p<=n) => R n -> (R p, R (n-p))
split (extract -> v) = ( mkR (subVector 0 p' v) ,
                         mkR (subVector p' (LA.size v - p') v) )
  where
    p' = fromIntegral . natVal $ (undefined :: Proxy p) :: Int


headTail :: (KnownNat n, 1<=n) => R n -> (ℝ, R (n-1))
headTail = ((!0) . extract *** id) . split


splitRows :: forall p m n . (KnownNat p, KnownNat m, KnownNat n, p<=m) => L m n -> (L p n, L (m-p) n)
splitRows (extract -> x) = ( mkL (takeRows p' x) ,
                             mkL (dropRows p' x) )
  where
    p' = fromIntegral . natVal $ (undefined :: Proxy p) :: Int

splitCols :: forall p m n. (KnownNat p, KnownNat m, KnownNat n, KnownNat (n-p), p<=n) => L m n -> (L m p, L m (n-p))
splitCols = (tr *** tr) . splitRows . tr


toRows :: forall m n . (KnownNat m, KnownNat n) => L m n -> [R n]
toRows (LA.toRows . extract -> vs) = map mkR vs

withRows
    :: forall n z . KnownNat n
    => [R n]
    -> (forall m . KnownNat m => L m n -> z)
    -> z
withRows (LA.fromRows . map extract -> m) f =
    case someNatVal $ fromIntegral $ LA.rows m of
       Nothing -> error "static/dynamic mismatch"
       Just (SomeNat (_ :: Proxy m)) -> f (mkL m :: L m n)

toColumns :: forall m n . (KnownNat m, KnownNat n) => L m n -> [R m]
toColumns (LA.toColumns . extract -> vs) = map mkR vs

withColumns
    :: forall m z . KnownNat m
    => [R m]
    -> (forall n . KnownNat n => L m n -> z)
    -> z
withColumns (LA.fromColumns . map extract -> m) f =
    case someNatVal $ fromIntegral $ LA.cols m of
       Nothing -> error "static/dynamic mismatch"
       Just (SomeNat (_ :: Proxy n)) -> f (mkL m :: L m n)



--------------------------------------------------------------------------------

build
  :: forall m n . (KnownNat n, KnownNat m)
    => (ℝ -> ℝ -> ℝ)
    -> L m n
build f = r
  where
    r = mkL $ LA.build (size r) f

--------------------------------------------------------------------------------

withVector
    :: forall z
     . Vector ℝ
    -> (forall n . (KnownNat n) => R n -> z)
    -> z
withVector v f =
    case someNatVal $ fromIntegral $ LA.size v of
       Nothing -> error "static/dynamic mismatch"
       Just (SomeNat (_ :: Proxy m)) -> f (mkR v :: R m)

-- | Useful for constraining two dependently typed vectors to match each
-- other in length when they are unknown at compile-time.
exactLength
    :: forall n m . (KnownNat n, KnownNat m)
    => R m
    -> Maybe (R n)
exactLength v =
    case sameNat (Proxy :: Proxy n) (Proxy :: Proxy m) of
      Just Refl -> Just v
      Nothing   -> Nothing

withMatrix
    :: forall z
     . Matrix ℝ
    -> (forall m n . (KnownNat m, KnownNat n) => L m n -> z)
    -> z
withMatrix a f =
    case someNatVal $ fromIntegral $ rows a of
       Nothing -> error "static/dynamic mismatch"
       Just (SomeNat (_ :: Proxy m)) ->
           case someNatVal $ fromIntegral $ cols a of
               Nothing -> error "static/dynamic mismatch"
               Just (SomeNat (_ :: Proxy n)) ->
                  f (mkL a :: L m n)

-- | Useful for constraining two dependently typed matrices to match each
-- other in dimensions when they are unknown at compile-time.
exactDims
    :: forall n m j k . (KnownNat n, KnownNat m, KnownNat j, KnownNat k)
    => L m n
    -> Maybe (L j k)
exactDims mat = do
    Refl <- sameNat (Proxy :: Proxy m) (Proxy :: Proxy j)
    Refl <- sameNat (Proxy :: Proxy n) (Proxy :: Proxy k)
    return mat

randomVector
    :: forall n . KnownNat n
    => Seed
    -> RandDist
    -> R n
randomVector s d = mkR (LA.randomVector s d
                          (fromInteger (natVal (Proxy :: Proxy n)))
                       )

rand
    :: forall m n . (KnownNat m, KnownNat n)
    => IO (L m n)
rand = mkL <$> LA.rand (fromInteger (natVal (Proxy :: Proxy m)))
                       (fromInteger (natVal (Proxy :: Proxy n)))

randn
    :: forall m n . (KnownNat m, KnownNat n)
    => IO (L m n)
randn = mkL <$> LA.randn (fromInteger (natVal (Proxy :: Proxy m)))
                         (fromInteger (natVal (Proxy :: Proxy n)))

gaussianSample
    :: forall m n . (KnownNat m, KnownNat n)
    => Seed
    -> R n
    -> Sym n
    -> L m n
gaussianSample s (extract -> mu) (Sym (extract -> sigma)) =
    mkL $ LA.gaussianSample s (fromInteger (natVal (Proxy :: Proxy m)))
                            mu (LA.trustSym sigma)

uniformSample
    :: forall m n . (KnownNat m, KnownNat n)
    => Seed
    -> R n    -- ^ minimums of each row
    -> R n    -- ^ maximums of each row
    -> L m n
uniformSample s (extract -> mins) (extract -> maxs) =
    mkL $ LA.uniformSample s (fromInteger (natVal (Proxy :: Proxy m)))
                           (zip (LA.toList mins) (LA.toList maxs))

meanCov
    :: forall m n . (KnownNat m, KnownNat n)
    => L m n
    -> (R n, Sym n)
meanCov (extract -> vs) = mkR *** (Sym . mkL . LA.unSym) $ LA.meanCov vs

--------------------------------------------------------------------------------

class Domain field vec mat | mat -> vec field, vec -> mat field, field -> mat vec
  where
    mul :: forall m k n. (KnownNat m, KnownNat k, KnownNat n) => mat m k -> mat k n -> mat m n
    app :: forall m n . (KnownNat m, KnownNat n) => mat m n -> vec n -> vec m
    dot :: forall n . (KnownNat n) => vec n -> vec n -> field
    cross :: vec 3 -> vec 3 -> vec 3
    diagR ::  forall m n k . (KnownNat m, KnownNat n, KnownNat k) => field -> vec k -> mat m n
    dvmap :: forall n. KnownNat n => (field -> field) -> vec n -> vec n
    dmmap :: forall n m. (KnownNat m, KnownNat n) => (field -> field) -> mat n m -> mat n m
    outer :: forall n m. (KnownNat m, KnownNat n) => vec n -> vec m -> mat n m
    zipWithVector :: forall n. KnownNat n => (field -> field -> field) -> vec n -> vec n -> vec n


instance Domain ℝ R L
  where
    mul = mulR
    app = appR
    dot = dotR
    cross = crossR
    diagR = diagRectR
    dvmap = mapR
    dmmap = mapL
    outer = outerR
    zipWithVector = zipWithR

instance Domain ℂ C M
  where
    mul = mulC
    app = appC
    dot = dotC
    cross = crossC
    diagR = diagRectC
    dvmap = mapC
    dmmap = mapM'
    outer = outerC
    zipWithVector = zipWithC

--------------------------------------------------------------------------------

mulR :: forall m k n. (KnownNat m, KnownNat k, KnownNat n) => L m k -> L k n -> L m n

mulR (isKonst -> Just (a,(_,k))) (isKonst -> Just (b,_)) = konst (a * b * fromIntegral k)

mulR (isDiag -> Just (0,a,_)) (isDiag -> Just (0,b,_)) = diagR 0 (mkR v :: R k)
  where
    v = a' * b'
    n = min (LA.size a) (LA.size b)
    a' = subVector 0 n a
    b' = subVector 0 n b

mulR (isDiag -> Just (0,a,_)) (extract -> b) = mkL (asColumn a * takeRows (LA.size a) b)

mulR (extract -> a) (isDiag -> Just (0,b,_)) = mkL (takeColumns (LA.size b) a * asRow b)

mulR a b = mkL (extract a LA.<> extract b)


appR :: (KnownNat m, KnownNat n) => L m n -> R n -> R m
appR (isDiag -> Just (0, w, _)) v = mkR (w * subVector 0 (LA.size w) (extract v))
appR m v = mkR (extract m LA.#> extract v)


dotR :: R n -> R n -> ℝ
dotR (ud1 -> u) (ud1 -> v)
    | singleV u || singleV v = sumElements (u * v)
    | otherwise = udot u v


crossR :: R 3 -> R 3 -> R 3
crossR (extract -> x) (extract -> y) = vec3 z1 z2 z3
  where
    z1 = x!1*y!2-x!2*y!1
    z2 = x!2*y!0-x!0*y!2
    z3 = x!0*y!1-x!1*y!0

outerR :: (KnownNat m, KnownNat n) => R n -> R m -> L n m
outerR (extract -> x) (extract -> y) = mkL (LA.outer x y)

mapR :: KnownNat n => (ℝ -> ℝ) -> R n -> R n
mapR f (unwrap -> v) = mkR (LA.cmap f v)

zipWithR :: KnownNat n => (ℝ -> ℝ -> ℝ) -> R n -> R n -> R n
zipWithR f (extract -> x) (extract -> y) = mkR (LA.zipVectorWith f x y)

mapL :: (KnownNat n, KnownNat m) => (ℝ -> ℝ) -> L n m -> L n m
mapL f (unwrap -> m) = mkL (LA.cmap f m)


--------------------------------------------------------------------------------

mulC :: forall m k n. (KnownNat m, KnownNat k, KnownNat n) => M m k -> M k n -> M m n

mulC (isKonstC -> Just (a,(_,k))) (isKonstC -> Just (b,_)) = konst (a * b * fromIntegral k)

mulC (isDiagC -> Just (0,a,_)) (isDiagC -> Just (0,b,_)) = diagR 0 (mkC v :: C k)
  where
    v = a' * b'
    n = min (LA.size a) (LA.size b)
    a' = subVector 0 n a
    b' = subVector 0 n b

mulC (isDiagC -> Just (0,a,_)) (extract -> b) = mkM (asColumn a * takeRows (LA.size a) b)

mulC (extract -> a) (isDiagC -> Just (0,b,_)) = mkM (takeColumns (LA.size b) a * asRow b)

mulC a b = mkM (extract a LA.<> extract b)


appC :: (KnownNat m, KnownNat n) => M m n -> C n -> C m
appC (isDiagC -> Just (0, w, _)) v = mkC (w * subVector 0 (LA.size w) (extract v))
appC m v = mkC (extract m LA.#> extract v)


dotC :: KnownNat n => C n -> C n -> ℂ
dotC (unwrap -> u) (unwrap -> v)
    | singleV u || singleV v = sumElements (conj u * v)
    | otherwise = u LA.<.> v


crossC :: C 3 -> C 3 -> C 3
crossC (extract -> x) (extract -> y) = mkC (LA.fromList [z1, z2, z3])
  where
    z1 = x!1*y!2-x!2*y!1
    z2 = x!2*y!0-x!0*y!2
    z3 = x!0*y!1-x!1*y!0

outerC :: (KnownNat m, KnownNat n) => C n -> C m -> M n m
outerC (extract -> x) (extract -> y) = mkM (LA.outer x y)

mapC :: KnownNat n => (ℂ -> ℂ) -> C n -> C n
mapC f (unwrap -> v) = mkC (LA.cmap f v)

zipWithC :: KnownNat n => (ℂ -> ℂ -> ℂ) -> C n -> C n -> C n
zipWithC f (extract -> x) (extract -> y) = mkC (LA.zipVectorWith f x y)

mapM' :: (KnownNat n, KnownNat m) => (ℂ -> ℂ) -> M n m -> M n m
mapM' f (unwrap -> m) = mkM (LA.cmap f m)


--------------------------------------------------------------------------------

diagRectR :: forall m n k . (KnownNat m, KnownNat n, KnownNat k) => ℝ -> R k -> L m n
diagRectR x v
    | m' == 1 = mkL (LA.diagRect x ev m' n')
    | m'*n' > 0 = r
    | otherwise = matrix []
  where
    r = mkL (asRow (vjoin [scalar x, ev, zeros]))
    ev = extract v
    zeros = LA.konst x (max 0 ((min m' n') - LA.size ev))
    (m',n') = size r


diagRectC :: forall m n k . (KnownNat m, KnownNat n, KnownNat k) => ℂ -> C k -> M m n
diagRectC x v
    | m' == 1 = mkM (LA.diagRect x ev m' n')
    | m'*n' > 0 = r
    | otherwise = fromList []
  where
    r = mkM (asRow (vjoin [scalar x, ev, zeros]))
    ev = extract v
    zeros = LA.konst x (max 0 ((min m' n') - LA.size ev))
    (m',n') = size r

--------------------------------------------------------------------------------

mean :: (KnownNat n, 1<=n) => R n -> ℝ
mean v = v <·> (1/dim)

test :: (Bool, IO ())
test = (ok,info)
  where
    ok =   extract (eye :: Sq 5) == ident 5
           && (unwrap .unSym) (mTm sm :: Sym 3) == tr ((3><3)[1..]) LA.<> (3><3)[1..]
           && unwrap (tm :: L 3 5) == LA.matrix 5 [1..15]
           && thingS == thingD
           && precS == precD
           && withVector (LA.vector [1..15]) sumV == sumElements (LA.fromList [1..15])

    info = do
        print $ u
        print $ v
        print (eye :: Sq 3)
        print $ ((u & 5) + 1) <·> v
        print (tm :: L 2 5)
        print (tm <> sm :: L 2 3)
        print thingS
        print thingD
        print precS
        print precD
        print $ withVector (LA.vector [1..15]) sumV
        splittest

    sumV w = w <·> konst 1

    u = vec2 3 5

    𝕧 x = vector [x] :: R 1

    v = 𝕧 2 & 4 & 7

    tm :: GL
    tm = lmat 0 [1..]

    lmat :: forall m n . (KnownNat m, KnownNat n) => ℝ -> [ℝ] -> L m n
    lmat z xs = r
      where
        r = mkL . reshape n' . LA.fromList . take (m'*n') $ xs ++ repeat z
        (m',n') = size r

    sm :: GSq
    sm = lmat 0 [1..]

    thingS = (u & 1) <·> tr q #> q #> v
      where
        q = tm :: L 10 3

    thingD = vjoin [ud1 u, 1] LA.<.> tr m LA.#> m LA.#> ud1 v
      where
        m = LA.matrix 3 [1..30]

    precS = (1::Double) + (2::Double) * ((1 :: R 3) * (u & 6)) <·> konst 2 #> v
    precD = 1 + 2 * vjoin[ud1 u, 6] LA.<.> LA.konst 2 (LA.size (ud1 u) +1, LA.size (ud1 v)) LA.#> ud1 v


splittest
    = do
    let v = range :: R 7
        a = snd (split v) :: R 4
    print $ a
    print $ snd . headTail . snd . headTail $ v
    print $ first (vec3 1 2 3)
    print $ second (vec3 1 2 3)
    print $ third (vec3 1 2 3)
    print $ (snd $ splitRows eye :: L 4 6)
 where
    first v = fst . headTail $ v
    second v = first . snd . headTail $ v
    third v = first . snd . headTail . snd . headTail $ v


instance (KnownNat n', KnownNat m') => Testable (L n' m')
  where
    checkT _ = test

--------------------------------------------------------------------------------

instance KnownNat n => Normed (R n)
  where
    norm_0 v = norm_0 (extract v)
    norm_1 v = norm_1 (extract v)
    norm_2 v = norm_2 (extract v)
    norm_Inf v = norm_Inf (extract v)

instance (KnownNat m, KnownNat n) => Normed (L m n)
  where
    norm_0 m = norm_0 (extract m)
    norm_1 m = norm_1 (extract m)
    norm_2 m = norm_2 (extract m)
    norm_Inf m = norm_Inf (extract m)
