module Type.Data.Rational where

import Prelude
import Data.Maybe (Maybe(..), isNothing)
import Data.Ratio ((%))
import Data.Ratio as DR
import Prim.Boolean (kind Boolean, True, False)
import Type.Data.Boolean (class And, class Not, class Or, BProxy)
import Unsafe.Coerce (unsafeCoerce)

----- kinds
foreign import kind InvokableRational

foreign import kind Rational

foreign import kind PInt

foreign import kind NInt

----- positive int type constructors
foreign import data POne :: PInt

foreign import data PSuc :: PInt -> PInt

----- positive int type constructors
foreign import data NOne :: NInt

foreign import data NSuc :: NInt -> NInt

----- rational number type constructors
foreign import data Zero :: Rational

foreign import data PRational :: PInt -> PInt -> Rational

foreign import data NRational :: NInt -> PInt -> Rational

infix 6 type PRational as /~

infix 6 type NRational as //~

----- constrained rational constructors
foreign import data LessThanConstraint :: Rational -> InvokableRational

foreign import data LessThanOrEqualToConstraint :: Rational -> InvokableRational

foreign import data NotConstraint :: InvokableRational -> InvokableRational

foreign import data AndConstraint :: InvokableRational -> InvokableRational -> InvokableRational

foreign import data OrConstraint :: InvokableRational -> InvokableRational -> InvokableRational

----- proxy for a rational
data CRProxy (r :: InvokableRational)
  = CRProxy

----- representation of a rational with numbers
data ConstrainedRatio (r :: InvokableRational) a b
  = CR a b

instance showConstrainedRatio :: (Show a, Show b) => Show (ConstrainedRatio r a b) where
  show (CR i j) = (show i) <> " % " <> (show j)

----- representation of a rational with integers
type ConstrainedRatioI r
  = ConstrainedRatio r Int Int

maximallyUnsafe :: forall a b c d. (a -> c) -> b -> d
maximallyUnsafe f x = unsafeCoerce $ f (unsafeCoerce x)

class TestRational (a :: InvokableRational) (b :: InvokableRational) (bool :: Boolean) | a b -> bool where
  invokeTest :: forall c. (BProxy bool) -> (CRProxy a -> c) -> CRProxy b -> c

instance testRational :: InvokableRationalRep a b bool => TestRational a b bool where
  invokeTest _ = maximallyUnsafe

class InvokableRational (a :: InvokableRational) (b :: InvokableRational) where
  invoke :: forall c. (ConstrainedRatioI a -> c) -> ConstrainedRatioI b -> c

class ConstrainedRational (a :: InvokableRational) where
  asConstraintedRational :: Int -> Int -> Maybe (ConstrainedRatioI a)

instance asConstraintedRationalOr :: (ConstrainedRational a, ConstrainedRational b) => ConstrainedRational (OrConstraint a b) where
  asConstraintedRational i j = (if isNothing x then y else x) :: Maybe (ConstrainedRatioI (OrConstraint a b))
    where
    f0 = asConstraintedRational :: Int -> Int -> Maybe (ConstrainedRatioI a)

    x = unsafeCoerce (f0 i j)

    f1 = asConstraintedRational :: Int -> Int -> Maybe (ConstrainedRatioI b)

    y = unsafeCoerce (f1 i j)

instance asConstraintedRationalAnd :: (ConstrainedRational a, ConstrainedRational b) => ConstrainedRational (AndConstraint a b) where
  asConstraintedRational i j = (if isNothing x then Nothing else y) :: Maybe (ConstrainedRatioI (AndConstraint a b))
    where
    f0 = asConstraintedRational :: Int -> Int -> Maybe (ConstrainedRatioI a)

    x = unsafeCoerce (f0 i j)

    f1 = asConstraintedRational :: Int -> Int -> Maybe (ConstrainedRatioI b)

    y = unsafeCoerce (f1 i j)

instance asConstraintedRationalNot :: (ConstrainedRational a) => ConstrainedRational (NotConstraint a) where
  asConstraintedRational i j = (if isNothing x && j /= 0 then Just (CR i j) else Nothing) :: Maybe (ConstrainedRatioI (NotConstraint a))
    where
    f0 = asConstraintedRational :: Int -> Int -> Maybe (ConstrainedRatioI a)

    x = f0 i j

instance asConstraintedRationalLessThanOrEqualTo :: Rational a => ConstrainedRational (LessThanOrEqualToConstraint a) where
  asConstraintedRational i j =
    ( if j /= 0
        && ( (i % j)
              <= (toRatio (toRational :: RatioI a))
          ) then
        Just (CR i j)
      else
        Nothing
    ) ::
      Maybe (ConstrainedRatioI (LessThanOrEqualToConstraint a))

instance asConstraintedRationalLessThanTo :: Rational a => ConstrainedRational (LessThanConstraint a) where
  asConstraintedRational i j =
    ( if j /= 0
        && ( (i % j)
              < (toRatio (toRational :: RatioI a))
          ) then
        Just (CR i j)
      else
        Nothing
    ) ::
      Maybe (ConstrainedRatioI (LessThanConstraint a))

instance constrainedRational :: InvokableRationalRep a b True => InvokableRational a b where
  invoke = maximallyUnsafe

class InvokableRationalRep (a :: InvokableRational) (b :: InvokableRational) (c :: Boolean) | a b -> c

-- two less thans can be compared
-- < 101 < 100
-- < 100 < 100
-- NOT < 99 < 100
instance rationalLessThan ::
  LessThanOrEqualTo b a c =>
  InvokableRationalRep (LessThanConstraint a) (LessThanConstraint b) c

-- two less than or equal tos can be compared
-- <= 101 <= 100
-- <= 100 <= 100
-- NOT <= 99 <= 100
instance rationalLessThanOrEqualTo ::
  LessThanOrEqualTo b a c =>
  InvokableRationalRep (LessThanOrEqualToConstraint a) (LessThanOrEqualToConstraint b) c

-- <= 101 < 100
-- <= 100 < 100
-- NOT <= 99 < 100
instance rationalLessThanOrEqualToLessThan ::
  LessThanOrEqualTo b a c =>
  InvokableRationalRep (LessThanOrEqualToConstraint a) (LessThanConstraint b) c

-- < 101 <= 100
-- NOT < 100 <= 100
-- NOT < 99 <= 100
instance rationalLessThanLessThanOrEqualTo ::
  LessThan b a c =>
  InvokableRationalRep (LessThanConstraint a) (LessThanOrEqualToConstraint b) c

-- same as flipping operation
instance rationalNotLessThan ::
  InvokableRationalRep (LessThanOrEqualToConstraint a) (LessThanOrEqualToConstraint b) c =>
  InvokableRationalRep (NotConstraint (LessThanConstraint a)) (NotConstraint (LessThanConstraint b)) c

-- same as flipping operation
instance rationalNotLessThanOrEqualTo ::
  InvokableRationalRep (LessThanConstraint a) (LessThanConstraint b) c =>
  InvokableRationalRep (NotConstraint (LessThanOrEqualToConstraint a)) (NotConstraint (LessThanOrEqualToConstraint b)) c

-- same as flipping operation
instance rationalNotLessThanOrEqualToLessThan ::
  InvokableRationalRep (LessThanConstraint a) (LessThanOrEqualToConstraint b) c =>
  InvokableRationalRep (NotConstraint (LessThanOrEqualToConstraint a)) (NotConstraint (LessThanConstraint b)) c

-- same as flipping operation
instance rationalNotLessThanLessThanOrEqualTo ::
  InvokableRationalRep (LessThanOrEqualToConstraint a) (LessThanConstraint b) c =>
  InvokableRationalRep (NotConstraint (LessThanConstraint a)) (NotConstraint (LessThanOrEqualToConstraint b)) c

-- the nots
instance rationalNotFalse0 ::
  InvokableRationalRep (NotConstraint (LessThanConstraint a)) (LessThanConstraint b) False

instance rationalNotFalse1 ::
  InvokableRationalRep (LessThanConstraint a) (NotConstraint (LessThanConstraint b)) False

instance rationalNotFalse2 ::
  InvokableRationalRep (NotConstraint (LessThanOrEqualToConstraint a)) (LessThanOrEqualToConstraint b) False

instance rationalNotFalse3 ::
  InvokableRationalRep (LessThanOrEqualToConstraint a) (NotConstraint (LessThanOrEqualToConstraint b)) False

instance rationalNotFalse4 ::
  InvokableRationalRep (NotConstraint (LessThanOrEqualToConstraint a)) (LessThanConstraint b) False

instance rationalNotFalse5 ::
  InvokableRationalRep (LessThanOrEqualToConstraint a) (NotConstraint (LessThanConstraint b)) False

instance rationalNotFalse6 ::
  InvokableRationalRep (NotConstraint (LessThanConstraint a)) (LessThanOrEqualToConstraint b) False

instance rationalNotFalse7 ::
  InvokableRationalRep (LessThanConstraint a) (NotConstraint (LessThanOrEqualToConstraint b)) False

-- not not
instance rationalNotNotL ::
  InvokableRationalRep a x c =>
  InvokableRationalRep (NotConstraint (NotConstraint a)) x c

instance rationalNotNotR0 ::
  InvokableRationalRep (LessThanConstraint x) a c =>
  InvokableRationalRep (LessThanConstraint x) (NotConstraint (NotConstraint a)) c

instance rationalNotNotR1 ::
  InvokableRationalRep (LessThanOrEqualToConstraint x) a c =>
  InvokableRationalRep (LessThanOrEqualToConstraint x) (NotConstraint (NotConstraint a)) c

instance rationalNotNotR2 ::
  (InvokableRationalRep x a c, InvokableRationalRep y a d, And c d e) =>
  InvokableRationalRep (AndConstraint x y) (NotConstraint (NotConstraint a)) e

instance rationalNotNotR3 ::
  (InvokableRationalRep x a c, InvokableRationalRep y a d, Or c d e) =>
  InvokableRationalRep (OrConstraint x y) (NotConstraint (NotConstraint a)) e

---- not and
instance rationalNotAndL ::
  ( InvokableRationalRep (NotConstraint a) x c
  , InvokableRationalRep (NotConstraint b) x d
  , Or c d e
  ) =>
  InvokableRationalRep (NotConstraint (AndConstraint a b)) x e

instance rationalNotAndR0 ::
  InvokableRationalRep
      (LessThanConstraint x)
      (OrConstraint (NotConstraint a) (NotConstraint b))
      e =>
  InvokableRationalRep (LessThanConstraint x) (NotConstraint (AndConstraint a b)) e

instance rationalNotAndR1 ::
  InvokableRationalRep
      (LessThanOrEqualToConstraint x)
      (OrConstraint (NotConstraint a) (NotConstraint b))
      e =>
  InvokableRationalRep (LessThanOrEqualToConstraint x) (NotConstraint (AndConstraint a b)) e

instance rationalNotAndR3 ::
  ( InvokableRationalRep x (OrConstraint (NotConstraint a) (NotConstraint b)) c
  , InvokableRationalRep y (OrConstraint (NotConstraint a) (NotConstraint b)) d
  , And c d e
  ) =>
  InvokableRationalRep (AndConstraint x y) (NotConstraint (AndConstraint a b)) e

instance rationalNotAndR4 ::
  ( InvokableRationalRep x (OrConstraint (NotConstraint a) (NotConstraint b)) c
  , InvokableRationalRep y (OrConstraint (NotConstraint a) (NotConstraint b)) d
  , Or c d e
  ) =>
  InvokableRationalRep (OrConstraint x y) (NotConstraint (AndConstraint a b)) e

-- not or
instance rationalNotOrL ::
  ( InvokableRationalRep (NotConstraint a) x c
  , InvokableRationalRep (NotConstraint b) x d
  , And c d e
  ) =>
  InvokableRationalRep (NotConstraint (OrConstraint a b)) x e

instance rationalNotOrR0 ::
  InvokableRationalRep
      (LessThanConstraint x)
      (AndConstraint (NotConstraint a) (NotConstraint b))
      c =>
  InvokableRationalRep (LessThanConstraint x) (NotConstraint (OrConstraint a b)) c

instance rationalNotOrR1 ::
  InvokableRationalRep
      (LessThanOrEqualToConstraint x)
      (AndConstraint (NotConstraint a) (NotConstraint b))
      c =>
  InvokableRationalRep (LessThanOrEqualToConstraint x) (NotConstraint (OrConstraint a b)) c

instance rationalNotOrR2 ::
  ( InvokableRationalRep x (AndConstraint (NotConstraint a) (NotConstraint b)) c
  , InvokableRationalRep y (AndConstraint (NotConstraint a) (NotConstraint b)) d
  , Or c d e
  ) =>
  InvokableRationalRep (OrConstraint x y) (NotConstraint (OrConstraint a b)) e

instance rationalNotOrR3 ::
  ( InvokableRationalRep x (AndConstraint (NotConstraint a) (NotConstraint b)) c
  , InvokableRationalRep y (AndConstraint (NotConstraint a) (NotConstraint b)) d
  , And c d e
  ) =>
  InvokableRationalRep (AndConstraint x y) (NotConstraint (OrConstraint a b)) e

-- the ands
instance rationalAndL0 ::
  ( InvokableRationalRep a (LessThanConstraint x) c
  , InvokableRationalRep b (LessThanConstraint x) d
  , And c d e
  ) =>
  InvokableRationalRep (AndConstraint a b) (LessThanConstraint x) e

instance rationalAndL1 ::
  ( InvokableRationalRep a (LessThanOrEqualToConstraint x) c
  , InvokableRationalRep b (LessThanOrEqualToConstraint x) d
  , And c d e
  ) =>
  InvokableRationalRep (AndConstraint a b) (LessThanOrEqualToConstraint x) e

instance rationalAndL3 ::
  ( InvokableRationalRep a (AndConstraint x y) c
  , InvokableRationalRep b (AndConstraint x y) d
  , And c d e
  ) =>
  InvokableRationalRep (AndConstraint a b) (AndConstraint x y) e

instance rationalAndL4 ::
  ( InvokableRationalRep a (OrConstraint x y) c
  , InvokableRationalRep b (OrConstraint x y) d
  , And c d e
  ) =>
  InvokableRationalRep (AndConstraint a b) (OrConstraint x y) e

instance rationalAndR0 ::
  ( AsLessThanConstraint
      (AndConstraint a b)
      c
      True
  , InvokableRationalRep (LessThanConstraint x) c f
  ) =>
  InvokableRationalRep (LessThanConstraint x) (AndConstraint a b) f

instance rationalAndnR0 ::
  ( AsNotLessThanConstraint
      (AndConstraint a b)
      c
      q
  , AsNotLessThanOrEqualToConstraint
      (AndConstraint a b)
      d
      r
  , NotLessThanSemigroup q r c d e
  , InvokableRationalRep (NotConstraint (LessThanConstraint x)) e f
  ) =>
  InvokableRationalRep (NotConstraint (LessThanConstraint x)) (AndConstraint a b) f

instance rationalAndR1 ::
  ( AsLessThanConstraint
      (AndConstraint a b)
      c
      q
  , AsLessThanOrEqualToConstraint
      (AndConstraint a b)
      d
      r
  , LessThanSemigroup q r c d e
  , InvokableRationalRep (LessThanOrEqualToConstraint x) e f
  ) =>
  InvokableRationalRep (LessThanOrEqualToConstraint x) (AndConstraint a b) f

instance rationalAndnR1 ::
  ( AsNotLessThanOrEqualToConstraint
      (AndConstraint a b)
      d
      True
  , InvokableRationalRep (NotConstraint (LessThanOrEqualToConstraint x)) d f
  ) =>
  InvokableRationalRep (NotConstraint (LessThanOrEqualToConstraint x)) (AndConstraint a b) f

instance rationalAndR4 ::
  ( InvokableRationalRep x (AndConstraint a b) c
  , InvokableRationalRep y (AndConstraint a b) d
  , Or c d e
  ) =>
  InvokableRationalRep (OrConstraint x y) (AndConstraint a b) e

-- the ors
instance rationalOrL0 ::
  ( InvokableRationalRep a (LessThanConstraint x) c
  , InvokableRationalRep b (LessThanConstraint x) d
  , Or c d e
  ) =>
  InvokableRationalRep (OrConstraint a b) (LessThanConstraint x) e

instance rationalOrL1 ::
  ( InvokableRationalRep a (LessThanOrEqualToConstraint x) c
  , InvokableRationalRep b (LessThanOrEqualToConstraint x) d
  , Or c d e
  ) =>
  InvokableRationalRep (OrConstraint a b) (LessThanOrEqualToConstraint x) e

instance rationalOrL4 ::
  ( InvokableRationalRep a (OrConstraint x y) c
  , InvokableRationalRep b (OrConstraint x y) d
  , Or c d e
  ) =>
  InvokableRationalRep (OrConstraint a b) (OrConstraint x y) e

instance rationalOrR0 ::
  ( AsLessThanConstraint
      (OrConstraint a b)
      c
      True
  , InvokableRationalRep (LessThanConstraint x) c f
  ) =>
  InvokableRationalRep (LessThanConstraint x) (OrConstraint a b) f

instance rationalOrnR0 ::
  ( AsNotLessThanConstraint
      (OrConstraint a b)
      c
      q
  , AsNotLessThanOrEqualToConstraint
      (OrConstraint a b)
      d
      r
  , NotLessThanSemigroup q r c d e
  , InvokableRationalRep (NotConstraint (LessThanConstraint x)) e f
  ) =>
  InvokableRationalRep (NotConstraint (LessThanConstraint x)) (OrConstraint a b) f

instance rationalOrR1 ::
  ( AsLessThanConstraint
      (OrConstraint a b)
      c
      q
  , AsLessThanOrEqualToConstraint
      (OrConstraint a b)
      d
      r
  , LessThanSemigroup q r c d e
  , InvokableRationalRep (LessThanOrEqualToConstraint x) e f
  ) =>
  InvokableRationalRep (LessThanOrEqualToConstraint x) (OrConstraint a b) f

instance rationalOrnR1 ::
  ( AsNotLessThanOrEqualToConstraint
      (OrConstraint a b)
      d
      True
  , InvokableRationalRep (NotConstraint (LessThanOrEqualToConstraint x)) d f
  ) =>
  InvokableRationalRep (NotConstraint (LessThanOrEqualToConstraint x)) (OrConstraint a b) f

class AsLessThanConstraint (a :: InvokableRational) (b :: InvokableRational) (c :: Boolean) | a -> b c

instance asLessThanConstraintLessThanConstraint :: AsLessThanConstraint (LessThanConstraint a) (LessThanConstraint a) True

instance asLessThanConstraintLessThanOrEqualToConstraint :: AsLessThanConstraint (LessThanOrEqualToConstraint a) (LessThanOrEqualToConstraint a) False

instance asLessThanConstraintNotConstraint ::
  AsNotLessThanConstraint a (NotConstraint b) v =>
  AsLessThanConstraint
    (NotConstraint a)
    b
    v

instance asLessThanConstraintAndConstraint ::
  ( AsLessThanConstraint a m q
  , AsLessThanConstraint b n r
  , Or q r True
  , Gate q m n (LessThanConstraint xx) -- monoid
  , Gate r n m (LessThanConstraint yy)
  , LessThan xx yy switch
  , Gate switch (LessThanConstraint xx) (LessThanConstraint yy) c
  ) =>
  AsLessThanConstraint (AndConstraint a b) c True

instance asLessThanConstraintOrConstraint ::
  ( AsLessThanConstraint a (LessThanConstraint x) q
  , AsLessThanConstraint b (LessThanConstraint y) r
  , And q r True
  , GreaterThan x y switch
  , Gate switch (LessThanConstraint x) (LessThanConstraint y) c
  , AsLessThanConstraint (LessThanConstraint x) c True
  ) =>
  AsLessThanConstraint (OrConstraint a b) c True

class Gate (a :: Boolean) (b :: InvokableRational) (c :: InvokableRational) (d :: InvokableRational) | a b c -> d

instance gateTrue :: Gate True b c b

instance gateFalse :: Gate False b c c

class GateR (a :: Boolean) (b :: Rational) (c :: Rational) (d :: Rational) | a b c -> d

instance gateRTrue :: GateR True b c b

instance gateRFalse :: GateR False b c c

class AsLessThanOrEqualToConstraint (a :: InvokableRational) (b :: InvokableRational) (c :: Boolean) | a -> b c

instance asLessThanOrEqualToConstraintLessThanConstraint :: AsLessThanOrEqualToConstraint (LessThanConstraint a) (LessThanConstraint a) False

instance asLessThanOrEqualToConstraintLessThanOrEqualToConstraint :: AsLessThanOrEqualToConstraint (LessThanOrEqualToConstraint a) (LessThanOrEqualToConstraint a) True

instance asLessThanOrEqualToConstraintNotConstraint ::
  AsNotLessThanOrEqualToConstraint a (NotConstraint b) v =>
  AsLessThanOrEqualToConstraint
    (NotConstraint a)
    b
    v

instance asLessThanOrEqualToConstraintAndConstraint ::
  ( AsLessThanOrEqualToConstraint a m q
  , AsLessThanOrEqualToConstraint b n r
  , Or q r True
  , Gate q m n (LessThanConstraint xx) -- monoid
  , Gate r n m (LessThanConstraint yy)
  , LessThanOrEqualTo xx yy switch
  , Gate switch (LessThanOrEqualToConstraint xx) (LessThanOrEqualToConstraint yy) c
  ) =>
  AsLessThanOrEqualToConstraint (AndConstraint a b) c True

instance asLessThanOrEqualToConstraintOrConstraint ::
  ( AsLessThanOrEqualToConstraint a (LessThanOrEqualToConstraint x) q
  , AsLessThanOrEqualToConstraint b (LessThanOrEqualToConstraint y) r
  , And q r True
  , GreaterThanOrEqualTo x y switch
  , Gate switch (LessThanOrEqualToConstraint x) (LessThanOrEqualToConstraint y) c
  ) =>
  AsLessThanOrEqualToConstraint (OrConstraint a b) c True

class AsNotLessThanConstraint (a :: InvokableRational) (b :: InvokableRational) (c :: Boolean) | a -> b c

instance asNotLessThanConstraintLessThanConstraint :: AsNotLessThanConstraint (LessThanConstraint a) b False

instance asNotLessThanConstraintLessThanOrEqualToConstraint :: AsNotLessThanConstraint (LessThanOrEqualToConstraint a) b False

instance asNotLessThanConstraintNotConstraint ::
  AsLessThanConstraint a b v =>
  AsNotLessThanConstraint
    (NotConstraint a)
    (NotConstraint b)
    v

instance asNotLessThanConstraintAndConstraint ::
  ( AsNotLessThanConstraint a m q
  , AsNotLessThanConstraint b n r
  , Or q r True
  , Gate q m n (LessThanConstraint xx) -- monoid
  , Gate r n m (LessThanConstraint yy)
  , GreaterThanOrEqualTo xx yy switch
  , Gate switch (NotConstraint (LessThanConstraint xx)) (NotConstraint (LessThanConstraint yy)) c
  ) =>
  AsNotLessThanConstraint (AndConstraint a b) c True

instance asNotLessThanConstraintOrConstraint ::
  ( AsNotLessThanConstraint a (NotConstraint (LessThanConstraint x)) q
  , AsNotLessThanConstraint b (NotConstraint (LessThanConstraint y)) r
  , And q r True
  , LessThanOrEqualTo x y switch
  , Gate switch (NotConstraint (LessThanConstraint x)) (NotConstraint (LessThanConstraint y)) c
  ) =>
  AsNotLessThanConstraint (OrConstraint a b) c True

class AsNotLessThanOrEqualToConstraint (a :: InvokableRational) (b :: InvokableRational) (c :: Boolean) | a -> b c

instance asNotLessThanOrEqualToConstraintLessThanConstraint :: AsNotLessThanOrEqualToConstraint (LessThanConstraint a) b False

instance asNotLessThanOrEqualToConstraintLessThanOrEqualToConstraint :: AsNotLessThanOrEqualToConstraint (LessThanOrEqualToConstraint a) b False

instance asNotLessThanOrEqualToConstraintNotConstraint ::
  AsNotLessThanOrEqualToConstraint a b v =>
  AsNotLessThanOrEqualToConstraint
    (NotConstraint a)
    (NotConstraint b)
    v

instance asNotLessThanOrEqualToConstraintAndConstraint ::
  ( AsNotLessThanOrEqualToConstraint a m q
  , AsNotLessThanOrEqualToConstraint b n r
  , Or q r True
  , Gate q m n (LessThanConstraint xx) -- monoid
  , Gate r n m (LessThanConstraint yy)
  , GreaterThan xx yy switch
  , Gate switch (NotConstraint (LessThanOrEqualToConstraint xx)) (NotConstraint (LessThanOrEqualToConstraint yy)) c
  ) =>
  AsNotLessThanOrEqualToConstraint (AndConstraint a b) c True

instance asNotLessThanOrEqualToConstraintOrConstraint ::
  ( AsNotLessThanOrEqualToConstraint a (NotConstraint (LessThanOrEqualToConstraint x)) q
  , AsNotLessThanOrEqualToConstraint b (NotConstraint (LessThanOrEqualToConstraint y)) r
  , And q r True
  , LessThan x y switch
  , Gate switch (NotConstraint (LessThanOrEqualToConstraint x)) (NotConstraint (LessThanOrEqualToConstraint y)) c
  ) =>
  AsNotLessThanOrEqualToConstraint (OrConstraint a b) c True

----------------------------
class LessThanSemigroup (x :: Boolean) (y :: Boolean) (a :: InvokableRational) (b :: InvokableRational) (c :: InvokableRational) | x y -> a b c

instance lessThanSemigroupTT :: LessThanSemigroup True True a b a

instance lessThanSemigroupTF :: LessThanSemigroup True False a b a

instance lessThanSemigroupFT :: LessThanSemigroup False True a b b

class NotLessThanSemigroup (x :: Boolean) (y :: Boolean) (a :: InvokableRational) (b :: InvokableRational) (c :: InvokableRational) | x y -> a b c

instance notLessThanSemigroupTT :: NotLessThanSemigroup True True a b a

instance notLessThanSemigroupTF :: NotLessThanSemigroup True False a b a

instance notLessThanSemigroupFT :: NotLessThanSemigroup False True a b b

----------------------------
-- a rational where only one value is inhabited
class ResolvableRational (a :: InvokableRational) (b :: Rational) | a -> b where
  resolve :: CRProxy a -> RatioI b

instance resolvableRational :: (PushNotsDown a aa, AreOrsToTop aa b, GatedLiftOrs b aa aaa, MergeAnds aaa aaaa, ResolvableRationalInternal aaaa res True, Rational res) => ResolvableRational a res where
  resolve _ = (toRational :: RatioI res)

class ResolvableRationalInternal (a :: InvokableRational) (b :: Rational) (bool :: Boolean) | a -> b bool

instance resolvableRationalLessThan :: ResolvableRationalInternal (LessThanConstraint n) Zero False

instance resolvableRationalLessThanOrEqualTo :: ResolvableRationalInternal (LessThanOrEqualToConstraint n) Zero False

instance resolvableRationalLessNot :: ResolvableRationalInternal (NotConstraint n) Zero False

instance resolvableRationalInternalAnd0 :: (Equal m n True) => ResolvableRationalInternal (AndConstraint (LessThanOrEqualToConstraint m) (NotConstraint (LessThanConstraint n))) n True

instance resolvableRationalInternalAnd1 :: (Equal m n True) => ResolvableRationalInternal (AndConstraint (NotConstraint (LessThanConstraint n)) (LessThanOrEqualToConstraint m)) n True

--
instance resolvableRationalInternalAnd2 :: ResolvableRationalInternal (AndConstraint (LessThanConstraint n) x) Zero False

instance resolvableRationalInternalAnd4 :: ResolvableRationalInternal (AndConstraint (AndConstraint q r) x) Zero False

instance resolvableRationalInternalAnd5 :: ResolvableRationalInternal (AndConstraint (OrConstraint q r) x) Zero False

instance resolvableRationalInternalAnd6 :: ResolvableRationalInternal (AndConstraint (LessThanOrEqualToConstraint x) (LessThanConstraint n)) Zero False

instance resolvableRationalInternalAnd7 :: ResolvableRationalInternal (AndConstraint (NotConstraint x) (LessThanConstraint n)) Zero False

---- to do, fill in all ands, perhaps some were missed?
---- only useful for testing, as the compiler will fail if not defined, which is what we want
---- but for testing, it's useful to test false values
--
instance resolvableRationalInternalOr :: (ResolvableRationalInternal a m True, ResolvableRationalInternal b n True, Equal m n True) => ResolvableRationalInternal (OrConstraint a b) n True

---- adds two rationals
---- uses rank-n types so that qualification can be partially applied
addConstrainedRationals ::
  forall (a :: InvokableRational) (x :: InvokableRational).
  InvokableRational a x =>
  ConstrainedRatioI a ->
  ( forall (b :: InvokableRational) (y :: InvokableRational).
    InvokableRational b y =>
    ConstrainedRatioI b ->
    ( forall (c :: InvokableRational).
      AddConstraint x y c =>
      ConstrainedRatioI c
    )
  )
addConstrainedRationals (CR a b) (CR x y) = let res = (a % b) + (x % y) in CR (DR.numerator res) (DR.denominator res)

infix 6 addConstrainedRationals as ~+~

------
------
------
------
------
------
------
------
------
------
type P1
  = POne

type P2
  = PSuc (P1)

type P3
  = PSuc (P2)

type P4
  = PSuc (P3)

type P5
  = PSuc (P4)

type P6
  = PSuc (P5)

type P7
  = PSuc (P6)

type P8
  = PSuc (P7)

type P9
  = PSuc (P8)

type P10
  = PSuc (P9)

type N1
  = NOne

type N2
  = NSuc (N1)

type N3
  = NSuc (N2)

type N4
  = NSuc (N3)

type N5
  = NSuc (N4)

type N6
  = NSuc (N5)

type N7
  = NSuc (N6)

type N8
  = NSuc (N7)

type N9
  = NSuc (N8)

-------------------
----- proxy for a rational
data RProxy (r :: Rational)
  = RProxy

----- flips a positive int to a negative int
class ToP (a :: NInt) (b :: PInt) | a -> b

instance toPOne :: ToP NOne POne

instance toPSuc :: ToP a b => ToP (NSuc a) (PSuc b)

----- flips a negative int to a negative int
class ToN (a :: PInt) (b :: NInt) | a -> b

instance toNOne :: ToN POne NOne

instance toNSuc :: ToN a b => ToN (PSuc a) (NSuc b)

----- flips a rational
class Flip (a :: Rational) (b :: Rational) | a -> b

instance flipZero :: Flip Zero Zero

instance flipP :: (ToN a c) => Flip (PRational a b) (NRational c b)

instance flipN :: (ToP a c) => Flip (NRational a b) (PRational c b)

----- adds two positive numbers
class PAdd (a :: PInt) (b :: PInt) (c :: PInt) | a b -> c

instance pAddOne :: PAdd POne b (PSuc b)

instance pAddSucc :: PAdd a b c => PAdd (PSuc a) b (PSuc c)

----- adds two negative numbers
class NAdd (a :: NInt) (b :: NInt) (c :: NInt) | a b -> c

instance nAddOne :: NAdd NOne b (NSuc b)

instance nAddSucc :: NAdd a b c => NAdd (NSuc a) b (NSuc c)

----- adds a positive and negative number, outputs a rational
class MAdd (a :: NInt) (b :: PInt) (c :: Rational) | a b -> c

instance mAdd11 :: MAdd NOne POne Zero

instance mAdd1S :: MAdd NOne (PSuc a) (PRational a POne)

instance mAddS1 :: MAdd (NSuc a) POne (NRational a POne)

instance mAddSS :: MAdd a b c => MAdd (NSuc a) (PSuc b) c

----- multiplies two positive numbers
class PMul (a :: PInt) (b :: PInt) (c :: PInt) | a b -> c

instance pMulOne :: PMul POne b b

instance pMulSucc :: (PMul a b c, PAdd c b d) => PMul (PSuc a) b d

----- multiplies two negative numbers
class NMul (a :: NInt) (b :: NInt) (c :: PInt) | a b -> c

instance nMulOne :: ToP b c => NMul NOne b c

instance nMulSucc :: (ToP x a, ToP y b, PMul a b c, PAdd c b d) => NMul (NSuc x) y d

----- multiplies a positive and negative number
class MMul (a :: PInt) (b :: NInt) (c :: NInt) | a b -> c

instance mMulOne :: MMul POne b b

instance mMulSucc :: (ToP y b, PMul a b c, PAdd c b d, ToN d z) => MMul (PSuc a) y z

----- is positive int x less than positive int y
class PLessThan (a :: PInt) (b :: PInt) (c :: Boolean) | a b -> c

instance pLessThan11 :: PLessThan POne POne False

instance pLessThan1S :: PLessThan POne (PSuc n) True

instance pLessThanS1 :: PLessThan (PSuc n) POne False

instance pLessThanSS :: PLessThan a b c ⇒ PLessThan (PSuc a) (PSuc b) c

----- is positive int x less than or equal to positive int y
class PLessThanOrEqualTo (a :: PInt) (b :: PInt) (c :: Boolean) | a b -> c

instance pLessThanOrEqualTo11 :: PLessThanOrEqualTo POne POne True

instance pLessThanOrEqualTo1S :: PLessThanOrEqualTo POne (PSuc n) True

instance pLessThanOrEqualToS1 :: PLessThanOrEqualTo (PSuc n) POne False

instance pLessThanOrEqualToSS :: PLessThanOrEqualTo a b c ⇒ PLessThanOrEqualTo (PSuc a) (PSuc b) c

----- is rational x less than rational y
class LessThan (a :: Rational) (b :: Rational) (c :: Boolean) | a b -> c

instance lessThanZP :: LessThan Zero (PRational a b) True

instance lessThanPZ :: LessThan (PRational a b) Zero False

instance lessThanZN :: LessThan Zero (NRational a b) False

instance lessThanNZ :: LessThan (NRational a b) Zero True

instance lessThanNP :: LessThan (NRational a b) (PRational c d) True

instance lessThanPN :: LessThan (PRational c d) (NRational a b) False

instance lessThanZZ :: LessThan Zero Zero False

instance lessThanNN :: (ToP a x, ToP c y, PMul x d e, PMul y b f, PLessThan f e z) => LessThan (NRational a b) (NRational c d) z

instance lessThanPP :: (PMul a d e, PMul c b f, PLessThan e f z) => LessThan (PRational a b) (PRational c d) z

----- is rational x less than or equal to rational y
class LessThanOrEqualTo (a :: Rational) (b :: Rational) (c :: Boolean) | a b -> c

instance lessThanOrEqualToZP :: LessThanOrEqualTo Zero (PRational a b) True

instance lessThanOrEqualToPZ :: LessThanOrEqualTo (PRational a b) Zero False

instance lessThanOrEqualToZN :: LessThanOrEqualTo Zero (NRational a b) False

instance lessThanOrEqualToNZ :: LessThanOrEqualTo (NRational a b) Zero True

instance lessThanOrEqualToNP :: LessThanOrEqualTo (NRational a b) (PRational c d) True

instance lessThanOrEqualToPN :: LessThanOrEqualTo (PRational c d) (NRational a b) False

instance lessThanOrEqualToZZ :: LessThanOrEqualTo Zero Zero True

instance lessThanOrEqualToNN :: (ToP a x, ToP c y, PMul x d e, PMul y b f, PLessThanOrEqualTo f e z) => LessThanOrEqualTo (NRational a b) (NRational c d) z

instance lessThanOrEqualToPP :: (PMul a d e, PMul c b f, PLessThanOrEqualTo e f z) => LessThanOrEqualTo (PRational a b) (PRational c d) z

----- is rational x greater than rational y
class GreaterThan (a :: Rational) (b :: Rational) (c :: Boolean) | a b -> c

instance greaterThan :: (LessThanOrEqualTo a b c, Not c d) => GreaterThan a b d

----- is rational x greater than or equal to rational y
class GreaterThanOrEqualTo (a :: Rational) (b :: Rational) (c :: Boolean) | a b -> c

instance greaterThanOrEqualTo :: (LessThan a b c, Not c d) => GreaterThanOrEqualTo a b d

----- is rational x equal to rational y
class Equal (a :: Rational) (b :: Rational) (c :: Boolean) | a b -> c

instance equal :: (GreaterThanOrEqualTo a b c, LessThanOrEqualTo a b d, And c d e) => Equal a b e

----- multiply two rationals
class Mul (a :: Rational) (b :: Rational) (c :: Rational) | a b -> c

instance mulZP :: Mul Zero (PRational a b) Zero

instance mulPZ :: Mul (PRational a b) Zero Zero

instance mulZN :: Mul Zero (NRational a b) Zero

instance mulNZ :: Mul (NRational a b) Zero Zero

instance mulNP :: (MMul n1 n0 n2, PMul d0 d1 d2) => Mul (NRational n0 d0) (PRational n1 d1) (NRational n2 d2)

instance mulPN :: (MMul n1 n0 n2, PMul d0 d1 d2) => Mul (PRational n1 d1) (NRational n0 d0) (NRational n2 d2)

instance mulZZ :: Mul Zero Zero Zero

instance mulNN :: (NMul n0 n1 n2, PMul d0 d1 d2) => Mul (NRational n0 d0) (NRational n1 d1) (PRational n2 d2)

instance mulPP :: (PMul n0 n1 n2, PMul d0 d1 d2) => Mul (PRational n0 d0) (PRational n1 d1) (PRational n2 d2)

class PrepForAdding (a :: InvokableRational) (b :: InvokableRational) | a -> b

instance prepForAdding :: (PushNotsDown a aa, AreOrsToTop aa b, GatedLiftOrs b aa aaa, MergeAnds aaa res) => PrepForAdding a res

class AddConstraint (a :: InvokableRational) (b :: InvokableRational) (c :: InvokableRational) | a b -> c

instance addConstraint :: (PrepForAdding a aa, PrepForAdding b bb, AddConstrainedValues aa bb res) => AddConstraint a b res

----- add two rationals
class AddConstrainedValues (a :: InvokableRational) (b :: InvokableRational) (c :: InvokableRational) | a b -> c

instance addConstrainedValuesLessThanConstraintLessThanConstraint :: Add a x c => AddConstrainedValues (LessThanConstraint a) (LessThanConstraint x) (LessThanConstraint c)

instance addConstrainedValuesLessThanConstraintLessThanOrEqualToConstraint :: Add a x c => AddConstrainedValues (LessThanConstraint a) (LessThanOrEqualToConstraint x) (LessThanConstraint c)

instance addConstrainedValuesLessThanConstraintNotConstraint0 :: AddConstrainedValues (LessThanConstraint a) (NotConstraint (LessThanConstraint x)) (OrConstraint (LessThanConstraint Zero) (NotConstraint (LessThanConstraint Zero)))

instance addConstrainedValuesLessThanConstraintNotConstraint1 :: AddConstrainedValues (LessThanConstraint a) (NotConstraint (LessThanOrEqualToConstraint x)) (OrConstraint (LessThanConstraint Zero) (NotConstraint (LessThanConstraint Zero)))

instance addConstrainedValuesLessThanConstraintAndConstraint0 :: (Add a y z) => AddConstrainedValues (LessThanConstraint a) (AndConstraint x (LessThanConstraint y)) (LessThanConstraint z)

instance addConstrainedValuesLessThanConstraintAndConstraint1 :: (Add a y z) => AddConstrainedValues (LessThanConstraint a) (AndConstraint x (LessThanOrEqualToConstraint y)) (LessThanConstraint z)

instance addConstrainedValuesLessThanConstraintOrConstraint :: (AddConstrainedValues (LessThanConstraint a) x q, AddConstrainedValues (LessThanConstraint a) y r) => AddConstrainedValues (LessThanConstraint a) (OrConstraint x y) (OrConstraint q r)

-- lte
instance addConstrainedValuesLessThanOrEqualToConstraintLessThanConstraint :: Add a x c => AddConstrainedValues (LessThanOrEqualToConstraint a) (LessThanConstraint x) (LessThanConstraint c)

instance addConstrainedValuesLessThanOrEqualToConstraintLessThanOrEqualToConstraint :: Add a x c => AddConstrainedValues (LessThanOrEqualToConstraint a) (LessThanOrEqualToConstraint x) (LessThanConstraint c)

instance addConstrainedValuesLessThanOrEqualToConstraintNotConstraint0 :: AddConstrainedValues (LessThanOrEqualToConstraint a) (NotConstraint (LessThanConstraint x)) (OrConstraint (LessThanConstraint Zero) (NotConstraint (LessThanConstraint Zero)))

instance addConstrainedValuesLessThanOrEqualToConstraintNotConstraint1 :: AddConstrainedValues (LessThanOrEqualToConstraint a) (NotConstraint (LessThanOrEqualToConstraint x)) (OrConstraint (LessThanConstraint Zero) (NotConstraint (LessThanConstraint Zero)))

instance addConstrainedValuesLessThanOrEqualToConstraintAndConstraint0 :: (Add a y z) => AddConstrainedValues (LessThanOrEqualToConstraint a) (AndConstraint x (LessThanConstraint y)) (LessThanConstraint z)

instance addConstrainedValuesLessThanOrEqualToConstraintAndConstraint1 :: (Add a y z) => AddConstrainedValues (LessThanOrEqualToConstraint a) (AndConstraint x (LessThanOrEqualToConstraint y)) (LessThanConstraint z)

instance addConstrainedValuesLessThanOrEqualToConstraintOrConstraint :: (AddConstrainedValues (LessThanOrEqualToConstraint a) x q, AddConstrainedValues (LessThanOrEqualToConstraint a) y r) => AddConstrainedValues (LessThanOrEqualToConstraint a) (OrConstraint x y) (OrConstraint q r)

--- not
instance addConstrainedValuesNotConstraintLessThanConstraint0 :: AddConstrainedValues (NotConstraint (LessThanConstraint a)) (LessThanConstraint x) (OrConstraint (LessThanConstraint Zero) (NotConstraint (LessThanConstraint Zero)))

instance addConstrainedValuesNotConstraintLessThanConstraint1 :: AddConstrainedValues (NotConstraint (LessThanOrEqualToConstraint a)) (LessThanConstraint x) (OrConstraint (LessThanConstraint Zero) (NotConstraint (LessThanConstraint Zero)))

instance addConstrainedValuesNotConstraintLessThanOrEqualToConstraint0 :: AddConstrainedValues (NotConstraint (LessThanConstraint a)) (LessThanOrEqualToConstraint x) (OrConstraint (LessThanConstraint Zero) (NotConstraint (LessThanConstraint Zero)))

instance addConstrainedValuesNotConstraintLessThanOrEqualToConstraint1 :: AddConstrainedValues (NotConstraint (LessThanOrEqualToConstraint a)) (LessThanOrEqualToConstraint x) (OrConstraint (LessThanConstraint Zero) (NotConstraint (LessThanConstraint Zero)))

instance addConstrainedValuesNotConstraintNotConstraint0 :: (Add a x c) => AddConstrainedValues (NotConstraint (LessThanConstraint a)) (NotConstraint (LessThanConstraint x)) (NotConstraint (LessThanConstraint c))

instance addConstrainedValuesNotConstraintNotConstraint1 :: (Add a x c) => AddConstrainedValues (NotConstraint (LessThanOrEqualToConstraint a)) (NotConstraint (LessThanConstraint x)) (NotConstraint (LessThanConstraint c))

instance addConstrainedValuesNotConstraintNotConstraint2 :: (Add a x c) => AddConstrainedValues (NotConstraint (LessThanConstraint a)) (NotConstraint (LessThanOrEqualToConstraint x)) (NotConstraint (LessThanConstraint c))

instance addConstrainedValuesNotConstraintNotConstraint3 :: (Add a x c) => AddConstrainedValues (NotConstraint (LessThanOrEqualToConstraint a)) (NotConstraint (LessThanOrEqualToConstraint x)) (NotConstraint (LessThanConstraint c))

----
instance addConstrainedValuesNotConstraintAndConstraint0 :: (Add a x c) => AddConstrainedValues (NotConstraint (LessThanConstraint a)) (AndConstraint (NotConstraint (LessThanConstraint x)) y) (NotConstraint (LessThanConstraint c))

instance addConstrainedValuesNotConstraintAndConstraint1 :: (Add a x c) => AddConstrainedValues (NotConstraint (LessThanOrEqualToConstraint a)) (AndConstraint (NotConstraint (LessThanConstraint x)) y) (NotConstraint (LessThanConstraint c))

instance addConstrainedValuesNotConstraintAndConstraint2 :: (Add a x c) => AddConstrainedValues (NotConstraint (LessThanConstraint a)) (AndConstraint (NotConstraint (LessThanOrEqualToConstraint x)) y) (NotConstraint (LessThanConstraint c))

instance addConstrainedValuesNotConstraintAndConstraint3 :: (Add a x c) => AddConstrainedValues (NotConstraint (LessThanOrEqualToConstraint a)) (AndConstraint (NotConstraint (LessThanOrEqualToConstraint x)) y) (NotConstraint (LessThanConstraint c))

----
instance addConstrainedValuesNotConstraintOrConstraint :: (AddConstrainedValues (NotConstraint a) x q, AddConstrainedValues (NotConstraint a) y r) => AddConstrainedValues (NotConstraint a) (OrConstraint x y) (OrConstraint q r)

instance addConstrainedValuesAndConstraintLessThanConstraint0 :: (Add b x c) => AddConstrainedValues (AndConstraint a (LessThanConstraint b)) (LessThanConstraint x) (LessThanConstraint c)

instance addConstrainedValuesAndConstraintLessThanConstraint1 :: (Add b x c) => AddConstrainedValues (AndConstraint a (LessThanOrEqualToConstraint b)) (LessThanConstraint x) (LessThanConstraint c)

instance addConstrainedValuesAndConstraintLessThanOrEqualToConstraint0 :: (Add b x c) => AddConstrainedValues (AndConstraint a (LessThanConstraint b)) (LessThanOrEqualToConstraint x) (LessThanConstraint c)

instance addConstrainedValuesAndConstraintLessThanOrEqualToConstraint1 :: (Add b x c) => AddConstrainedValues (AndConstraint a (LessThanOrEqualToConstraint b)) (LessThanOrEqualToConstraint x) (LessThanConstraint c)

instance addConstrainedValuesAndConstraintNotConstraint0 :: (Add a x c) => AddConstrainedValues (AndConstraint (NotConstraint (LessThanConstraint a)) b) (NotConstraint (LessThanConstraint x)) (NotConstraint (LessThanConstraint c))

instance addConstrainedValuesAndConstraintNotConstraint1 :: (Add a x c) => AddConstrainedValues (AndConstraint (NotConstraint (LessThanOrEqualToConstraint a)) b) (NotConstraint (LessThanConstraint x)) (NotConstraint (LessThanConstraint c))

instance addConstrainedValuesAndConstraintNotConstraint2 :: (Add a x c) => AddConstrainedValues (AndConstraint (NotConstraint (LessThanConstraint a)) b) (NotConstraint (LessThanOrEqualToConstraint x)) (NotConstraint (LessThanConstraint c))

instance addConstrainedValuesAndConstraintNotConstraint3 :: (Add a x c) => AddConstrainedValues (AndConstraint (NotConstraint (LessThanOrEqualToConstraint a)) b) (NotConstraint (LessThanOrEqualToConstraint x)) (NotConstraint (LessThanConstraint c))

instance addConstrainedValuesAndConstraintAndConstraint0 :: (Add a x q, Add b y r) => AddConstrainedValues (AndConstraint (NotConstraint (LessThanConstraint a)) (LessThanConstraint b)) (AndConstraint (NotConstraint (LessThanConstraint x)) (LessThanConstraint y)) (AndConstraint (NotConstraint (LessThanConstraint q)) (LessThanConstraint r))

instance addConstrainedValuesAndConstraintAndConstraint1 :: (Add a x q, Add b y r) => AddConstrainedValues (AndConstraint (NotConstraint (LessThanConstraint a)) (LessThanConstraint b)) (AndConstraint (NotConstraint (LessThanConstraint x)) (LessThanOrEqualToConstraint y)) (AndConstraint (NotConstraint (LessThanConstraint q)) (LessThanConstraint r))

instance addConstrainedValuesAndConstraintAndConstraint2 :: (Add a x q, Add b y r) => AddConstrainedValues (AndConstraint (NotConstraint (LessThanConstraint a)) (LessThanConstraint b)) (AndConstraint (NotConstraint (LessThanOrEqualToConstraint x)) (LessThanConstraint y)) (AndConstraint (NotConstraint (LessThanConstraint q)) (LessThanConstraint r))

instance addConstrainedValuesAndConstraintAndConstraint3 :: (Add a x q, Add b y r) => AddConstrainedValues (AndConstraint (NotConstraint (LessThanConstraint a)) (LessThanConstraint b)) (AndConstraint (NotConstraint (LessThanOrEqualToConstraint x)) (LessThanOrEqualToConstraint y)) (AndConstraint (NotConstraint (LessThanConstraint q)) (LessThanConstraint r))

instance addConstrainedValuesAndConstraintAndConstraint4 :: (Add a x q, Add b y r) => AddConstrainedValues (AndConstraint (NotConstraint (LessThanConstraint a)) (LessThanOrEqualToConstraint b)) (AndConstraint (NotConstraint (LessThanConstraint x)) (LessThanConstraint y)) (AndConstraint (NotConstraint (LessThanConstraint q)) (LessThanConstraint r))

instance addConstrainedValuesAndConstraintAndConstraint5 :: (Add a x q, Add b y r) => AddConstrainedValues (AndConstraint (NotConstraint (LessThanConstraint a)) (LessThanOrEqualToConstraint b)) (AndConstraint (NotConstraint (LessThanConstraint x)) (LessThanOrEqualToConstraint y)) (AndConstraint (NotConstraint (LessThanConstraint q)) (LessThanConstraint r))

instance addConstrainedValuesAndConstraintAndConstraint6 :: (Add a x q, Add b y r) => AddConstrainedValues (AndConstraint (NotConstraint (LessThanConstraint a)) (LessThanOrEqualToConstraint b)) (AndConstraint (NotConstraint (LessThanOrEqualToConstraint x)) (LessThanConstraint y)) (AndConstraint (NotConstraint (LessThanConstraint q)) (LessThanConstraint r))

instance addConstrainedValuesAndConstraintAndConstraint7 :: (Add a x q, Add b y r) => AddConstrainedValues (AndConstraint (NotConstraint (LessThanConstraint a)) (LessThanOrEqualToConstraint b)) (AndConstraint (NotConstraint (LessThanOrEqualToConstraint x)) (LessThanOrEqualToConstraint y)) (AndConstraint (NotConstraint (LessThanConstraint q)) (LessThanConstraint r))

instance addConstrainedValuesAndConstraintAndConstraint8 :: (Add a x q, Add b y r) => AddConstrainedValues (AndConstraint (NotConstraint (LessThanOrEqualToConstraint a)) (LessThanConstraint b)) (AndConstraint (NotConstraint (LessThanConstraint x)) (LessThanConstraint y)) (AndConstraint (NotConstraint (LessThanConstraint q)) (LessThanConstraint r))

instance addConstrainedValuesAndConstraintAndConstraint9 :: (Add a x q, Add b y r) => AddConstrainedValues (AndConstraint (NotConstraint (LessThanOrEqualToConstraint a)) (LessThanConstraint b)) (AndConstraint (NotConstraint (LessThanConstraint x)) (LessThanOrEqualToConstraint y)) (AndConstraint (NotConstraint (LessThanConstraint q)) (LessThanConstraint r))

instance addConstrainedValuesAndConstraintAndConstraint10 :: (Add a x q, Add b y r) => AddConstrainedValues (AndConstraint (NotConstraint (LessThanOrEqualToConstraint a)) (LessThanConstraint b)) (AndConstraint (NotConstraint (LessThanOrEqualToConstraint x)) (LessThanConstraint y)) (AndConstraint (NotConstraint (LessThanConstraint q)) (LessThanConstraint r))

instance addConstrainedValuesAndConstraintAndConstraint11 :: (Add a x q, Add b y r) => AddConstrainedValues (AndConstraint (NotConstraint (LessThanOrEqualToConstraint a)) (LessThanConstraint b)) (AndConstraint (NotConstraint (LessThanOrEqualToConstraint x)) (LessThanOrEqualToConstraint y)) (AndConstraint (NotConstraint (LessThanConstraint q)) (LessThanConstraint r))

instance addConstrainedValuesAndConstraintAndConstraint12 :: (Add a x q, Add b y r) => AddConstrainedValues (AndConstraint (NotConstraint (LessThanOrEqualToConstraint a)) (LessThanOrEqualToConstraint b)) (AndConstraint (NotConstraint (LessThanConstraint x)) (LessThanConstraint y)) (AndConstraint (NotConstraint (LessThanConstraint q)) (LessThanConstraint r))

instance addConstrainedValuesAndConstraintAndConstraint13 :: (Add a x q, Add b y r) => AddConstrainedValues (AndConstraint (NotConstraint (LessThanOrEqualToConstraint a)) (LessThanOrEqualToConstraint b)) (AndConstraint (NotConstraint (LessThanConstraint x)) (LessThanOrEqualToConstraint y)) (AndConstraint (NotConstraint (LessThanConstraint q)) (LessThanConstraint r))

instance addConstrainedValuesAndConstraintAndConstraint14 :: (Add a x q, Add b y r) => AddConstrainedValues (AndConstraint (NotConstraint (LessThanOrEqualToConstraint a)) (LessThanOrEqualToConstraint b)) (AndConstraint (NotConstraint (LessThanOrEqualToConstraint x)) (LessThanConstraint y)) (AndConstraint (NotConstraint (LessThanConstraint q)) (LessThanConstraint r))

instance addConstrainedValuesAndConstraintAndConstraint15 :: (Add a x q, Add b y r) => AddConstrainedValues (AndConstraint (NotConstraint (LessThanOrEqualToConstraint a)) (LessThanOrEqualToConstraint b)) (AndConstraint (NotConstraint (LessThanOrEqualToConstraint x)) (LessThanOrEqualToConstraint y)) (AndConstraint (NotConstraint (LessThanConstraint q)) (LessThanConstraint r))

instance addConstrainedValuesAndConstraintOrConstraint :: (AddConstrainedValues (AndConstraint a b) x q, AddConstrainedValues (AndConstraint a b) y r) => AddConstrainedValues (AndConstraint a b) (OrConstraint x y) (OrConstraint q r)

instance addConstrainedValuesOrConstraintLessThanConstraint :: (AddConstrainedValues a (LessThanConstraint x) q, AddConstrainedValues y (LessThanConstraint x) r) => AddConstrainedValues (OrConstraint a b) (LessThanConstraint x) (OrConstraint q r)

instance addConstrainedValuesOrConstraintLessThanOrEqualToConstraint :: (AddConstrainedValues a (LessThanOrEqualToConstraint x) q, AddConstrainedValues y (LessThanOrEqualToConstraint x) r) => AddConstrainedValues (OrConstraint a b) (LessThanOrEqualToConstraint x) (OrConstraint q r)

instance addConstrainedValuesOrConstraintNotConstraint :: (AddConstrainedValues a (NotConstraint x) q, AddConstrainedValues y (NotConstraint x) r) => AddConstrainedValues (OrConstraint a b) (NotConstraint x) (OrConstraint q r)

instance addConstrainedValuesOrConstraintAndConstraint :: (AddConstrainedValues a (AndConstraint x y) q, AddConstrainedValues y (AndConstraint x y) r) => AddConstrainedValues (OrConstraint a b) (AndConstraint x y) (OrConstraint q r)

instance addConstrainedValuesOrConstraintOrConstraint :: (AddConstrainedValues a x m, AddConstrainedValues a y n, AddConstrainedValues b x o, AddConstrainedValues b y p) => AddConstrainedValues (OrConstraint a b) (OrConstraint x y) (OrConstraint (OrConstraint m n) (OrConstraint o p))

class AreOrsToTop (a :: InvokableRational) (b :: Boolean) | a -> b

-- will only execute at the toplevel
instance areOrsToTopOr :: (AreOrsToTop a x, AreOrsToTop b y, And x y z) => AreOrsToTop (OrConstraint a b) z

-- lt
instance areOrsToTopLessThanConstraint :: AreOrsToTop (LessThanConstraint x) True

-- lte
instance areOrsToTopLessThanOrEqualToConstraint :: AreOrsToTop (LessThanOrEqualToConstraint x) True

-- not
instance areOrsToTopNotLessThanConstraint :: AreOrsToTop (NotConstraint (LessThanConstraint x)) True

instance areOrsToTopNotLessThanOrEqualToConstraint :: AreOrsToTop (NotConstraint (LessThanOrEqualToConstraint x)) True

instance areOrsToTopNotNot :: AreOrsToTop x z => AreOrsToTop (NotConstraint (NotConstraint x)) z

instance areOrsToTopNotAnd :: (AreOrsToTop a x, AreOrsToTop b y, And x y z) => AreOrsToTop (NotConstraint (AndConstraint a b)) z

instance areOrsToTopNotOr :: AreOrsToTop (NotConstraint (OrConstraint a b)) False

-- and
instance areOrsToTopAndLessThanConstraintLessThanConstraint :: AreOrsToTop (AndConstraint (LessThanConstraint a) (LessThanConstraint x)) True

instance areOrsToTopAndLessThanConstraintLessThanOrEqualToConstraint :: AreOrsToTop (AndConstraint (LessThanConstraint a) (LessThanOrEqualToConstraint x)) True

instance areOrsToTopAndLessThanConstraintNotConstraint :: (AreOrsToTop x z) => AreOrsToTop (AndConstraint (LessThanConstraint a) (NotConstraint x)) z

instance areOrsToTopAndLessThanConstraintAndConstraint :: (AreOrsToTop x m, AreOrsToTop y n, And m n z) => AreOrsToTop (AndConstraint (LessThanConstraint a) (AndConstraint x y)) z

instance areOrsToTopAndLessThanConstraintOrConstraint :: AreOrsToTop (AndConstraint (LessThanConstraint a) (OrConstraint x y)) False

instance areOrsToTopAndLessThanOrEqualToConstraintLessThanConstraint :: AreOrsToTop (AndConstraint (LessThanOrEqualToConstraint a) (LessThanConstraint x)) True

instance areOrsToTopAndLessThanOrEqualToConstraintLessThanOrEqualToConstraint :: AreOrsToTop (AndConstraint (LessThanOrEqualToConstraint a) (LessThanOrEqualToConstraint x)) True

instance areOrsToTopAndLessThanOrEqualToConstraintNotConstraint :: (AreOrsToTop x z) => AreOrsToTop (AndConstraint (LessThanOrEqualToConstraint a) (NotConstraint x)) z

instance areOrsToTopAndLessThanOrEqualToConstraintAndConstraint :: (AreOrsToTop x m, AreOrsToTop y n, And m n z) => AreOrsToTop (AndConstraint (LessThanOrEqualToConstraint a) (AndConstraint x y)) z

instance areOrsToTopAndLessThanOrEqualToConstraintOrConstraint :: AreOrsToTop (AndConstraint (LessThanOrEqualToConstraint a) (OrConstraint x y)) False

instance areOrsToTopAndNotConstraintLessThanConstraint :: (AreOrsToTop a z) => AreOrsToTop (AndConstraint (NotConstraint a) (LessThanConstraint x)) z

instance areOrsToTopAndNotConstraintLessThanOrEqualToConstraint :: (AreOrsToTop a z) => AreOrsToTop (AndConstraint (NotConstraint a) (LessThanOrEqualToConstraint x)) z

instance areOrsToTopAndNotConstraintNotConstraint :: (AreOrsToTop a m, AreOrsToTop x n, And m n z) => AreOrsToTop (AndConstraint (NotConstraint a) (NotConstraint x)) z

instance areOrsToTopAndNotConstraintAndConstraint :: (AreOrsToTop a m, AreOrsToTop x n, AreOrsToTop y o, And m n f, And f o z) => AreOrsToTop (AndConstraint (NotConstraint a) (AndConstraint x y)) z

instance areOrsToTopAndNotConstraintOrConstraint :: AreOrsToTop (AndConstraint (NotConstraint a) (OrConstraint x y)) False

instance areOrsToTopAndAndConstraintLessThanConstraint :: (AreOrsToTop a m, AreOrsToTop b n, And m n z) => AreOrsToTop (AndConstraint (AndConstraint a b) (LessThanConstraint x)) z

instance areOrsToTopAndAndConstraintLessThanOrEqualToConstraint :: (AreOrsToTop a m, AreOrsToTop b n, And m n z) => AreOrsToTop (AndConstraint (AndConstraint a b) (LessThanOrEqualToConstraint x)) z

instance areOrsToTopAndAndConstraintNotConstraint :: (AreOrsToTop a m, AreOrsToTop b n, AreOrsToTop x o, And m n f, And f o z) => AreOrsToTop (AndConstraint (AndConstraint a b) (NotConstraint x)) z

instance areOrsToTopAndAndConstraintAndConstraint :: (AreOrsToTop a m, AreOrsToTop b n, AreOrsToTop x o, AreOrsToTop y p, And m n f, And f o q, And q p z) => AreOrsToTop (AndConstraint (AndConstraint a b) (AndConstraint x y)) z

instance areOrsToTopAndAndConstraintOrConstraint :: AreOrsToTop (AndConstraint (AndConstraint a b) (OrConstraint x y)) False

instance areOrsToTopAndOrConstraintLessThanConstraint :: AreOrsToTop (AndConstraint (OrConstraint a b) (LessThanConstraint x)) False

instance areOrsToTopAndOrConstraintLessThanOrEqualToConstraint :: AreOrsToTop (AndConstraint (OrConstraint a b) (LessThanOrEqualToConstraint x)) False

instance areOrsToTopAndOrConstraintNotConstraint :: AreOrsToTop (AndConstraint (OrConstraint a b) (NotConstraint x)) False

instance areOrsToTopAndOrConstraintAndConstraint :: AreOrsToTop (AndConstraint (OrConstraint a b) (AndConstraint x y)) False

instance areOrsToTopAndOrConstraintOrConstraint :: AreOrsToTop (AndConstraint (OrConstraint a b) (OrConstraint x y)) False

class GatedLiftOrs (gate :: Boolean) (maybeLift :: InvokableRational) (res :: InvokableRational) | gate maybeLift -> res

instance gatedLiftOrsTrue :: GatedLiftOrs True x x

instance gatedLiftOrsFalse :: (LiftOrs x y, AreOrsToTop y b, GatedLiftOrs b y z) => GatedLiftOrs False x z

-- lift ors
class LiftOrs (a :: InvokableRational) (b :: InvokableRational) | a -> b

-- will only execute at the toplevel
instance liftOrsOr :: (LiftOrs a x, LiftOrs b y) => LiftOrs (OrConstraint a b) (OrConstraint x y)

-- lt
instance liftOrsLessThanConstraint :: LiftOrs (LessThanConstraint x) (LessThanConstraint x)

-- lte
instance liftOrsLessThanOrEqualToConstraint :: LiftOrs (LessThanOrEqualToConstraint x) (LessThanOrEqualToConstraint x)

-- not
instance liftOrsNotLessThanConstraint :: LiftOrs (NotConstraint (LessThanConstraint x)) (NotConstraint (LessThanConstraint x))

instance liftOrsNotLessThanOrEqualToConstraint :: LiftOrs (NotConstraint (LessThanOrEqualToConstraint x)) (NotConstraint (LessThanOrEqualToConstraint x))

instance liftOrsNotNot :: LiftOrs x z => LiftOrs (NotConstraint (NotConstraint x)) (NotConstraint (NotConstraint z))

instance liftOrsNotAnd :: (LiftOrs a x, LiftOrs b y) => LiftOrs (NotConstraint (AndConstraint a b)) (NotConstraint (AndConstraint x y))

instance liftOrsNotOr :: (LiftOrs a x, LiftOrs b y) => LiftOrs (NotConstraint (OrConstraint a b)) (AndConstraint (NotConstraint x) (NotConstraint y))

-- and
instance liftOrsAndLessThanConstraintLessThanConstraint :: LiftOrs (AndConstraint (LessThanConstraint a) (LessThanConstraint x)) (AndConstraint (LessThanConstraint a) (LessThanConstraint x))

instance liftOrsAndLessThanConstraintLessThanOrEqualToConstraint :: LiftOrs (AndConstraint (LessThanConstraint a) (LessThanOrEqualToConstraint x)) (AndConstraint (LessThanConstraint a) (LessThanOrEqualToConstraint x))

instance liftOrsAndLessThanConstraintNotConstraint :: (LiftOrs x z) => LiftOrs (AndConstraint (LessThanConstraint a) (NotConstraint x)) (AndConstraint (LessThanConstraint a) (NotConstraint z))

instance liftOrsAndLessThanConstraintAndConstraint :: (LiftOrs x m, LiftOrs y n) => LiftOrs (AndConstraint (LessThanConstraint a) (AndConstraint x y)) (AndConstraint (LessThanConstraint a) (AndConstraint m n))

instance liftOrsAndLessThanConstraintOrConstraint :: LiftOrs (AndConstraint (LessThanConstraint a) (OrConstraint x y)) (OrConstraint (AndConstraint (LessThanConstraint a) x) (AndConstraint (LessThanConstraint a) y))

instance liftOrsAndLessThanOrEqualToConstraintLessThanConstraint :: LiftOrs (AndConstraint (LessThanOrEqualToConstraint a) (LessThanConstraint x)) (AndConstraint (LessThanOrEqualToConstraint a) (LessThanConstraint x))

instance liftOrsAndLessThanOrEqualToConstraintLessThanOrEqualToConstraint :: LiftOrs (AndConstraint (LessThanOrEqualToConstraint a) (LessThanOrEqualToConstraint x)) (AndConstraint (LessThanOrEqualToConstraint a) (LessThanOrEqualToConstraint x))

instance liftOrsAndLessThanOrEqualToConstraintNotConstraint :: (LiftOrs x z) => LiftOrs (AndConstraint (LessThanOrEqualToConstraint a) (NotConstraint x)) (AndConstraint (LessThanOrEqualToConstraint a) (NotConstraint z))

instance liftOrsAndLessThanOrEqualToConstraintAndConstraint :: (LiftOrs x m, LiftOrs y n) => LiftOrs (AndConstraint (LessThanOrEqualToConstraint a) (AndConstraint x y)) (AndConstraint (LessThanOrEqualToConstraint a) (AndConstraint m n))

instance liftOrsAndLessThanOrEqualToConstraintOrConstraint :: LiftOrs (AndConstraint (LessThanOrEqualToConstraint a) (OrConstraint x y)) (OrConstraint (AndConstraint (LessThanOrEqualToConstraint a) x) (AndConstraint (LessThanOrEqualToConstraint a) y))

instance liftOrsAndNotConstraintLessThanConstraint :: (LiftOrs a z) => LiftOrs (AndConstraint (NotConstraint a) (LessThanConstraint x)) (AndConstraint (NotConstraint z) (LessThanConstraint x))

instance liftOrsAndNotConstraintLessThanOrEqualToConstraint :: (LiftOrs a z) => LiftOrs (AndConstraint (NotConstraint a) (LessThanOrEqualToConstraint x)) (AndConstraint (NotConstraint z) (LessThanOrEqualToConstraint x))

instance liftOrsAndNotConstraintNotConstraint :: (LiftOrs a m, LiftOrs x n) => LiftOrs (AndConstraint (NotConstraint a) (NotConstraint x)) (AndConstraint (NotConstraint m) (NotConstraint n))

instance liftOrsAndNotConstraintAndConstraint :: (LiftOrs a m, LiftOrs x n, LiftOrs y o) => LiftOrs (AndConstraint (NotConstraint a) (AndConstraint x y)) (AndConstraint (NotConstraint m) (AndConstraint n o))

instance liftOrsAndNotConstraintOrConstraint :: (LiftOrs a z) => LiftOrs (AndConstraint (NotConstraint a) (OrConstraint x y)) (OrConstraint (AndConstraint (NotConstraint z) x) (AndConstraint (NotConstraint z) y))

instance liftOrsAndAndConstraintLessThanConstraint :: (LiftOrs a m, LiftOrs b n) => LiftOrs (AndConstraint (AndConstraint a b) (LessThanConstraint x)) (AndConstraint (AndConstraint m n) (LessThanConstraint x))

instance liftOrsAndAndConstraintLessThanOrEqualToConstraint :: (LiftOrs a m, LiftOrs b n) => LiftOrs (AndConstraint (AndConstraint a b) (LessThanOrEqualToConstraint x)) (AndConstraint (AndConstraint m n) (LessThanOrEqualToConstraint x))

instance liftOrsAndAndConstraintNotConstraint :: (LiftOrs a m, LiftOrs b n, LiftOrs x o) => LiftOrs (AndConstraint (AndConstraint a b) (NotConstraint x)) (AndConstraint (AndConstraint m n) (NotConstraint o))

instance liftOrsAndAndConstraintAndConstraint :: (LiftOrs a m, LiftOrs b n, LiftOrs x o, LiftOrs y p) => LiftOrs (AndConstraint (AndConstraint a b) (AndConstraint x y)) (AndConstraint (AndConstraint m n) (AndConstraint o p))

instance liftOrsAndAndConstraintOrConstraint :: (LiftOrs a m, LiftOrs b n, LiftOrs x o, LiftOrs y p) => LiftOrs (AndConstraint (AndConstraint a b) (OrConstraint x y)) (OrConstraint (AndConstraint (AndConstraint m n) o) (AndConstraint (AndConstraint m n) p))

instance liftOrsAndOrConstraintLessThanConstraint :: (LiftOrs a m, LiftOrs b n) => LiftOrs (AndConstraint (OrConstraint a b) (LessThanConstraint x)) (OrConstraint (AndConstraint m (LessThanConstraint x)) (AndConstraint n (LessThanConstraint x)))

instance liftOrsAndOrConstraintLessThanOrEqualToConstraint :: (LiftOrs a m, LiftOrs b n) => LiftOrs (AndConstraint (OrConstraint a b) (LessThanOrEqualToConstraint x)) (OrConstraint (AndConstraint m (LessThanOrEqualToConstraint x)) (AndConstraint n (LessThanOrEqualToConstraint x)))

instance liftOrsAndOrConstraintNotConstraint :: (LiftOrs a m, LiftOrs b n, LiftOrs q x) => LiftOrs (AndConstraint (OrConstraint a b) (NotConstraint q)) (OrConstraint (AndConstraint m (NotConstraint x)) (AndConstraint n (NotConstraint x)))

instance liftOrsAndOrConstraintAndConstraint :: (LiftOrs a m, LiftOrs b n, LiftOrs x o, LiftOrs y p) => LiftOrs (AndConstraint (OrConstraint x y) (AndConstraint a b)) (OrConstraint (AndConstraint o (AndConstraint m n)) (AndConstraint p (AndConstraint m n)))

instance liftOrsAndOrConstraintOrConstraint :: (LiftOrs a m, LiftOrs b n, LiftOrs x o, LiftOrs y p) => LiftOrs (AndConstraint (OrConstraint x y) (OrConstraint a b)) (OrConstraint (OrConstraint (AndConstraint o m) (AndConstraint o n)) (OrConstraint (AndConstraint p m) (AndConstraint p n)))

-- push nots
class PushNotsDown (a :: InvokableRational) (b :: InvokableRational) | a -> b

instance pushNotsDownLessThanConstraint :: PushNotsDown (LessThanConstraint x) (LessThanConstraint x)

instance pushNotsDownLessThanOrEqualToConstraint :: PushNotsDown (LessThanOrEqualToConstraint x) (LessThanOrEqualToConstraint x)

instance pushNotsDownNotLessThanConstraint :: PushNotsDown (NotConstraint (LessThanConstraint x)) (NotConstraint (LessThanConstraint x))

instance pushNotsDownNotLessThanOrEqualToConstraint :: PushNotsDown (NotConstraint (LessThanOrEqualToConstraint x)) (NotConstraint (LessThanOrEqualToConstraint x))

instance pushNotsDownNotNotConstraint :: PushNotsDown y z => PushNotsDown (NotConstraint (NotConstraint y)) z

instance pushNotsDownNotAndConstraint :: (PushNotsDown (NotConstraint a) c, PushNotsDown (NotConstraint b) d) => PushNotsDown (NotConstraint (AndConstraint a b)) (OrConstraint c d)

instance pushNotsDownNotOrConstraint :: (PushNotsDown (NotConstraint a) c, PushNotsDown (NotConstraint b) d) => PushNotsDown (NotConstraint (OrConstraint a b)) (AndConstraint c d)

instance pushNotsDownAnd :: (PushNotsDown a x, PushNotsDown b y) => PushNotsDown (AndConstraint a b) (AndConstraint x y)

instance pushNotsDownOr :: (PushNotsDown a x, PushNotsDown b y) => PushNotsDown (OrConstraint a b) (OrConstraint x y)

class MergeAnds (a :: InvokableRational) (b :: InvokableRational) | a -> b

instance mergeAndsLessThan :: MergeAnds (LessThanConstraint x) (LessThanConstraint x)

instance mergeAndsLessThanOrEqualTo :: MergeAnds (LessThanOrEqualToConstraint x) (LessThanOrEqualToConstraint x)

instance mergeAndsNot :: MergeAnds x y => MergeAnds (NotConstraint x) (NotConstraint y)

instance mergeAndsLessThanConstraintLessThanConstraint :: (LessThan a x b, GateR b a x c) => MergeAnds (AndConstraint (LessThanConstraint a) (LessThanConstraint x)) (LessThanConstraint c)

instance mergeAndsLessThanConstraintLessThanOrEqualToConstraint :: (LessThan a x b, LessThan x a c, Gate b (LessThanConstraint a) (LessThanOrEqualToConstraint x) d, Gate c (LessThanOrEqualToConstraint x) d f) => MergeAnds (AndConstraint (LessThanConstraint a) (LessThanOrEqualToConstraint x)) f

-- not
instance mergeAndsLessThanConstraintNotConstraintLessThanConstraint :: MergeAnds (AndConstraint (LessThanConstraint a) (NotConstraint (LessThanConstraint x))) (AndConstraint (NotConstraint (LessThanConstraint x)) (LessThanConstraint a))

instance mergeAndsLessThanConstraintNotConstraintLessThanOrEqualToConstraint :: MergeAnds (AndConstraint (LessThanConstraint a) (NotConstraint (LessThanOrEqualToConstraint x))) (AndConstraint (NotConstraint (LessThanOrEqualToConstraint x)) (LessThanConstraint a))

instance mergeAndsLessThanConstraintNotConstraintNotConstraint :: (MergeAnds x y, MergeAnds (AndConstraint (LessThanConstraint a) y) z) => MergeAnds (AndConstraint (LessThanConstraint a) (NotConstraint (NotConstraint x))) z

instance mergeAndsLessThanConstraintNotConstraintAndConstraint :: MergeAnds (AndConstraint (LessThanConstraint a) (OrConstraint (NotConstraint x) (NotConstraint y))) z => MergeAnds (AndConstraint (LessThanConstraint a) (NotConstraint (AndConstraint x y))) z

instance mergeAndsLessThanConstraintNotConstraintOrConstraint :: MergeAnds (AndConstraint (LessThanConstraint a) (AndConstraint (NotConstraint x) (NotConstraint y))) z => MergeAnds (AndConstraint (LessThanConstraint a) (NotConstraint (OrConstraint x y))) z

-- end not
instance mergeAndsLessThanConstraintAndConstraint :: (MergeAnds (AndConstraint x y) z, MergeAnds (AndConstraint (LessThanConstraint a) z) m) => MergeAnds (AndConstraint (LessThanConstraint a) (AndConstraint x y)) m

instance mergeAndsLessThanConstraintOrConstraint :: (MergeAnds (OrConstraint x y) z, MergeAnds (AndConstraint (LessThanConstraint a) z) m) => MergeAnds (AndConstraint (LessThanConstraint a) (OrConstraint x y)) m

------------- leq
instance mergeAndsLessThanOrEqualToConstraintLessThanOrEqualToConstraint :: (LessThan a x b, Gate b (LessThanConstraint a) (LessThanOrEqualToConstraint x) d) => MergeAnds (AndConstraint (LessThanOrEqualToConstraint x) (LessThanConstraint a)) d

instance mergeAndsLessThanOrEqualToConstraintLessThanConstraint :: (LessThan a x b, GateR b a x c) => MergeAnds (AndConstraint (LessThanOrEqualToConstraint a) (LessThanOrEqualToConstraint x)) (LessThanOrEqualToConstraint c)

-- not
instance mergeAndsLessThanOrEqualToConstraintNotConstraintLessThanConstraint :: MergeAnds (AndConstraint (LessThanOrEqualToConstraint a) (NotConstraint (LessThanConstraint x))) (AndConstraint (NotConstraint (LessThanConstraint x)) (LessThanOrEqualToConstraint a))

instance mergeAndsLessThanOrEqualToConstraintNotConstraintLessThanOrEqualToConstraint :: MergeAnds (AndConstraint (LessThanOrEqualToConstraint a) (NotConstraint (LessThanOrEqualToConstraint x))) (AndConstraint (NotConstraint (LessThanOrEqualToConstraint x)) (LessThanOrEqualToConstraint a))

instance mergeAndsLessThanOrEqualToConstraintNotConstraintNotConstraint :: (MergeAnds x y, MergeAnds (AndConstraint (LessThanOrEqualToConstraint a) y) z) => MergeAnds (AndConstraint (LessThanOrEqualToConstraint a) (NotConstraint (NotConstraint x))) z

instance mergeAndsLessThanOrEqualToConstraintNotConstraintAndConstraint :: MergeAnds (AndConstraint (LessThanOrEqualToConstraint a) (OrConstraint (NotConstraint x) (NotConstraint y))) z => MergeAnds (AndConstraint (LessThanOrEqualToConstraint a) (NotConstraint (AndConstraint x y))) z

instance mergeAndsLessThanOrEqualToConstraintNotConstraintOrConstraint :: MergeAnds (AndConstraint (LessThanOrEqualToConstraint a) (AndConstraint (NotConstraint x) (NotConstraint y))) z => MergeAnds (AndConstraint (LessThanOrEqualToConstraint a) (NotConstraint (OrConstraint x y))) z

-- end not
instance mergeAndsLessThanOrEqualToConstraintAndConstraint :: (MergeAnds (AndConstraint x y) z, MergeAnds (AndConstraint (LessThanOrEqualToConstraint a) z) m) => MergeAnds (AndConstraint (LessThanOrEqualToConstraint a) (AndConstraint x y)) m

instance mergeAndsLessThanOrEqualToConstraintOrConstraint :: (MergeAnds (OrConstraint x y) z, MergeAnds (AndConstraint (LessThanOrEqualToConstraint a) z) m) => MergeAnds (AndConstraint (LessThanOrEqualToConstraint a) (OrConstraint x y)) m

------------ not
------------------ lt
instance mergeAndsConstraintNotLessThanConstraintLessThanConstraint :: MergeAnds (AndConstraint (NotConstraint (LessThanConstraint a)) (LessThanConstraint x)) (AndConstraint (NotConstraint (LessThanConstraint a)) (LessThanConstraint x))

instance mergeAndsConstraintNotLessThanOrEqualToConstraintLessThanConstraint :: MergeAnds (AndConstraint (NotConstraint (LessThanOrEqualToConstraint a)) (LessThanConstraint x)) (AndConstraint (NotConstraint (LessThanOrEqualToConstraint a)) (LessThanConstraint x))

instance mergeAndsConstraintNotNotConstraintLessThanConstraint :: (MergeAnds a b, MergeAnds (AndConstraint b (LessThanConstraint x)) z) => MergeAnds (AndConstraint (NotConstraint (NotConstraint a)) (LessThanConstraint x)) z

instance mergeAndsConstraintNotAndConstraintLessThanConstraint :: (MergeAnds (OrConstraint (NotConstraint a) (NotConstraint b)) c, MergeAnds (AndConstraint c (LessThanConstraint x)) z) => MergeAnds (AndConstraint (NotConstraint (AndConstraint a b)) (LessThanConstraint x)) z

instance mergeAndsConstraintNotOrConstraintLessThanConstraint :: (MergeAnds (AndConstraint (NotConstraint a) (NotConstraint b)) c, MergeAnds (AndConstraint c (LessThanConstraint x)) z) => MergeAnds (AndConstraint (NotConstraint (OrConstraint a b)) (LessThanConstraint x)) z

------------------- lte
instance mergeAndsConstraintNotLessThanConstraintLessThanOrEqualToConstraint :: MergeAnds (AndConstraint (NotConstraint (LessThanConstraint a)) (LessThanOrEqualToConstraint x)) (AndConstraint (NotConstraint (LessThanConstraint a)) (LessThanOrEqualToConstraint x))

instance mergeAndsConstraintNotLessThanOrEqualToConstraintLessThanOrEqualToConstraint :: MergeAnds (AndConstraint (NotConstraint (LessThanOrEqualToConstraint x)) (LessThanOrEqualToConstraint a)) (AndConstraint (NotConstraint (LessThanOrEqualToConstraint x)) (LessThanOrEqualToConstraint a))

instance mergeAndsConstraintNotNotConstraintLessThanOrEqualToConstraint :: (MergeAnds a b, MergeAnds (AndConstraint b (LessThanOrEqualToConstraint x)) z) => MergeAnds (AndConstraint (NotConstraint (NotConstraint a)) (LessThanOrEqualToConstraint x)) z

instance mergeAndsConstraintNotAndConstraintLessThanOrEqualToConstraint :: (MergeAnds (OrConstraint (NotConstraint a) (NotConstraint b)) c, MergeAnds (AndConstraint c (LessThanOrEqualToConstraint x)) z) => MergeAnds (AndConstraint (NotConstraint (AndConstraint a b)) (LessThanOrEqualToConstraint x)) z

instance mergeAndsConstraintNotOrConstraintLessThanOrEqualToConstraint :: (MergeAnds (AndConstraint (NotConstraint a) (NotConstraint b)) c, MergeAnds (AndConstraint c (LessThanOrEqualToConstraint x)) z) => MergeAnds (AndConstraint (NotConstraint (OrConstraint a b)) (LessThanOrEqualToConstraint x)) z

----------------- not
instance mergeAndsConstraintNotLessThanConstraintNotLessThanConstraint :: (GreaterThan a x b, GateR b a x c) => MergeAnds (AndConstraint (NotConstraint (LessThanConstraint a)) (NotConstraint (LessThanConstraint x))) (NotConstraint (LessThanConstraint c))

instance mergeAndsConstraintNotLessThanConstraintNotLessThanOrEqualToConstraint :: (GreaterThan a x b, Gate b (NotConstraint (LessThanConstraint a)) (NotConstraint (LessThanOrEqualToConstraint x)) f) => MergeAnds (AndConstraint (NotConstraint (LessThanConstraint a)) (NotConstraint (LessThanOrEqualToConstraint x))) f

instance mergeAndsConstraintNotLessThanConstraintNotNotConstraint :: (MergeAnds x y, MergeAnds (AndConstraint (NotConstraint (LessThanConstraint a)) y) z) => MergeAnds (AndConstraint (NotConstraint (LessThanConstraint a)) (NotConstraint (NotConstraint x))) z

instance mergeAndsConstraintNotLessThanConstraintNotAndConstraint :: (MergeAnds (OrConstraint (NotConstraint x) (NotConstraint y)) c, MergeAnds (AndConstraint (NotConstraint (LessThanConstraint a)) c) z) => MergeAnds (AndConstraint (NotConstraint (LessThanConstraint a)) (NotConstraint (AndConstraint x y))) z

instance mergeAndsConstraintNotLessThanConstraintNotOrConstraint :: (MergeAnds (AndConstraint (NotConstraint x) (NotConstraint y)) c, MergeAnds (AndConstraint (NotConstraint (LessThanConstraint a)) c) z) => MergeAnds (AndConstraint (NotConstraint (LessThanConstraint a)) (NotConstraint (OrConstraint x y))) z

-----
instance mergeAndsConstraintNotLessThanOrEqualToConstraintNotLessThanConstraint :: (GreaterThan a x b, Gate b (NotConstraint (LessThanOrEqualToConstraint a)) (NotConstraint (LessThanConstraint x)) f) => MergeAnds (AndConstraint (NotConstraint (LessThanOrEqualToConstraint a)) (NotConstraint (LessThanConstraint x))) f

instance mergeAndsConstraintNotLessThanOrEqualToConstraintNotLessThanOrEqualToConstraint :: (GreaterThan a x b, GateR b a x c) => MergeAnds (AndConstraint (NotConstraint (LessThanOrEqualToConstraint a)) (NotConstraint (LessThanOrEqualToConstraint x))) (NotConstraint (LessThanOrEqualToConstraint c))

instance mergeAndsConstraintNotLessThanOrEqualToConstraintNotNotConstraint :: (MergeAnds x y, MergeAnds (AndConstraint (NotConstraint (LessThanOrEqualToConstraint a)) y) z) => MergeAnds (AndConstraint (NotConstraint (LessThanOrEqualToConstraint a)) (NotConstraint (NotConstraint x))) z

instance mergeAndsConstraintNotLessThanOrEqualToConstraintNotAndConstraint :: (MergeAnds (OrConstraint (NotConstraint x) (NotConstraint y)) c, MergeAnds (AndConstraint (NotConstraint (LessThanOrEqualToConstraint a)) c) z) => MergeAnds (AndConstraint (NotConstraint (LessThanOrEqualToConstraint a)) (NotConstraint (AndConstraint x y))) z

instance mergeAndsConstraintNotLessThanOrEqualToConstraintNotOrConstraint :: (MergeAnds (AndConstraint (NotConstraint x) (NotConstraint y)) c, MergeAnds (AndConstraint (NotConstraint (LessThanOrEqualToConstraint a)) c) z) => MergeAnds (AndConstraint (NotConstraint (LessThanOrEqualToConstraint a)) (NotConstraint (OrConstraint x y))) z

-----
instance mergeAndsConstraintNotNotConstraintNotLessThanConstraint :: (MergeAnds a b, MergeAnds (AndConstraint b (NotConstraint (LessThanConstraint x))) z) => MergeAnds (AndConstraint (NotConstraint (NotConstraint a)) (NotConstraint (LessThanConstraint x))) z

instance mergeAndsConstraintNotNotConstraintNotLessThanOrEqualToConstraint :: (MergeAnds a b, MergeAnds (AndConstraint b (NotConstraint (LessThanOrEqualToConstraint x))) z) => MergeAnds (AndConstraint (NotConstraint (NotConstraint a)) (NotConstraint (LessThanOrEqualToConstraint x))) z

instance mergeAndsConstraintNotNotConstraintNotNotConstraint :: (MergeAnds a b, MergeAnds x y, MergeAnds (AndConstraint b y) z) => MergeAnds (AndConstraint (NotConstraint (NotConstraint a)) (NotConstraint (NotConstraint x))) z

instance mergeAndsConstraintNotNotConstraintNotAndConstraint :: (MergeAnds a b, MergeAnds (OrConstraint (NotConstraint x) (NotConstraint y)) q, MergeAnds (AndConstraint b q) z) => MergeAnds (AndConstraint (NotConstraint (NotConstraint a)) (NotConstraint (AndConstraint x y))) z

instance mergeAndsConstraintNotNotConstraintNotOrConstraint :: (MergeAnds a b, MergeAnds (AndConstraint (NotConstraint x) (NotConstraint y)) q, MergeAnds (AndConstraint b q) z) => MergeAnds (AndConstraint (NotConstraint (NotConstraint a)) (NotConstraint (OrConstraint x y))) z

--------------
instance mergeAndsConstraintNotAndConstraintNotLessThanConstraint :: (MergeAnds (OrConstraint (NotConstraint a) (NotConstraint b)) c, MergeAnds (AndConstraint c (NotConstraint (LessThanConstraint x))) z) => MergeAnds (AndConstraint (NotConstraint (AndConstraint a b)) (NotConstraint (LessThanConstraint x))) z

instance mergeAndsConstraintNotAndConstraintNotLessThanOrEqualToConstraint :: (MergeAnds (OrConstraint (NotConstraint a) (NotConstraint b)) c, MergeAnds (AndConstraint c (NotConstraint (LessThanOrEqualToConstraint x))) z) => MergeAnds (AndConstraint (NotConstraint (AndConstraint a b)) (NotConstraint (LessThanOrEqualToConstraint x))) z

instance mergeAndsConstraintNotAndConstraintNotNotConstraint :: (MergeAnds (OrConstraint (NotConstraint a) (NotConstraint b)) c, MergeAnds x y, MergeAnds (AndConstraint c y) z) => MergeAnds (AndConstraint (NotConstraint (AndConstraint a b)) (NotConstraint (NotConstraint x))) z

instance mergeAndsConstraintNotAndConstraintNotAndConstraint :: (MergeAnds (OrConstraint (NotConstraint a) (NotConstraint b)) c, MergeAnds (OrConstraint (NotConstraint x) (NotConstraint y)) q, MergeAnds (AndConstraint c q) z) => MergeAnds (AndConstraint (NotConstraint (AndConstraint a b)) (NotConstraint (AndConstraint x y))) z

instance mergeAndsConstraintNotAndConstraintNotOrConstraint :: (MergeAnds (OrConstraint (NotConstraint a) (NotConstraint b)) c, MergeAnds (AndConstraint (NotConstraint x) (NotConstraint y)) q, MergeAnds (AndConstraint c q) z) => MergeAnds (AndConstraint (NotConstraint (AndConstraint a b)) (NotConstraint (OrConstraint x y))) z

-----------------------
instance mergeAndsConstraintNotOrConstraintNotLessThanConstraint :: (MergeAnds (AndConstraint (NotConstraint a) (NotConstraint b)) c, MergeAnds (AndConstraint c (NotConstraint (LessThanConstraint x))) z) => MergeAnds (AndConstraint (NotConstraint (OrConstraint a b)) (NotConstraint (LessThanConstraint x))) z

instance mergeAndsConstraintNotOrConstraintNotLessThanOrEqualToConstraint :: (MergeAnds (AndConstraint (NotConstraint a) (NotConstraint b)) c, MergeAnds (AndConstraint c (NotConstraint (LessThanOrEqualToConstraint x))) z) => MergeAnds (AndConstraint (NotConstraint (OrConstraint a b)) (NotConstraint (LessThanOrEqualToConstraint x))) z

instance mergeAndsConstraintNotOrConstraintNotNotConstraint :: (MergeAnds (AndConstraint (NotConstraint a) (NotConstraint b)) c, MergeAnds x y, MergeAnds (AndConstraint c y) z) => MergeAnds (AndConstraint (NotConstraint (OrConstraint a b)) (NotConstraint (NotConstraint x))) z

instance mergeAndsConstraintNotOrConstraintNotAndConstraint :: (MergeAnds (AndConstraint (NotConstraint a) (NotConstraint b)) c, MergeAnds (OrConstraint (NotConstraint x) (NotConstraint y)) q, MergeAnds (AndConstraint c q) z) => MergeAnds (AndConstraint (NotConstraint (OrConstraint a b)) (NotConstraint (AndConstraint x y))) z

instance mergeAndsConstraintNotOrConstraintNotOrConstraint :: (MergeAnds (AndConstraint (NotConstraint a) (NotConstraint b)) c, MergeAnds (AndConstraint (NotConstraint x) (NotConstraint y)) q, MergeAnds (AndConstraint c q) z) => MergeAnds (AndConstraint (NotConstraint (OrConstraint a b)) (NotConstraint (OrConstraint x y))) z

----------------- and
instance mergeAndsConstraintNotLessThanConstraintAndConstraint :: (MergeAnds (AndConstraint x y) q, MergeAnds (AndConstraint (NotConstraint (LessThanConstraint a)) q) z) => MergeAnds (AndConstraint (NotConstraint (LessThanConstraint a)) (AndConstraint x y)) z

instance mergeAndsConstraintNotLessThanOrEqualToConstraintAndConstraint :: (MergeAnds (AndConstraint x y) q, MergeAnds (AndConstraint (NotConstraint (LessThanOrEqualToConstraint a)) q) z) => MergeAnds (AndConstraint (NotConstraint (LessThanOrEqualToConstraint a)) (AndConstraint x y)) z

instance mergeAndsConstraintNotNotConstraintAndConstraint :: (MergeAnds (AndConstraint x y) q, MergeAnds a b, MergeAnds (AndConstraint b q) z) => MergeAnds (AndConstraint (NotConstraint (NotConstraint a)) (AndConstraint x y)) z

instance mergeAndsConstraintNotAndConstraintAndConstraint :: (MergeAnds (AndConstraint x y) q, MergeAnds (OrConstraint (NotConstraint a) (NotConstraint b)) c, MergeAnds (AndConstraint c q) z) => MergeAnds (AndConstraint (NotConstraint (AndConstraint a b)) (AndConstraint x y)) z

instance mergeAndsConstraintNotOrConstraintAndConstraint :: (MergeAnds (AndConstraint x y) q, MergeAnds (AndConstraint (NotConstraint a) (NotConstraint b)) c, MergeAnds (AndConstraint c q) z) => MergeAnds (AndConstraint (NotConstraint (OrConstraint a b)) (AndConstraint x y)) z

-------------------- or
instance mergeAndsConstraintNotLessThanConstraintOrConstraint :: (MergeAnds (OrConstraint x y) q, MergeAnds (AndConstraint (NotConstraint (LessThanConstraint a)) q) z) => MergeAnds (AndConstraint (NotConstraint (LessThanConstraint a)) (OrConstraint x y)) z

instance mergeAndsConstraintNotLessThanOrEqualToConstraintOrConstraint :: (MergeAnds (OrConstraint x y) q, MergeAnds (AndConstraint (NotConstraint (LessThanOrEqualToConstraint a)) q) z) => MergeAnds (AndConstraint (NotConstraint (LessThanOrEqualToConstraint a)) (OrConstraint x y)) z

instance mergeAndsConstraintNotNotConstraintOrConstraint :: (MergeAnds (OrConstraint x y) q, MergeAnds a b, MergeAnds (AndConstraint b q) z) => MergeAnds (AndConstraint (NotConstraint (NotConstraint a)) (OrConstraint x y)) z

instance mergeAndsConstraintNotAndConstraintOrConstraint :: (MergeAnds (OrConstraint x y) q, MergeAnds (OrConstraint (NotConstraint a) (NotConstraint b)) c, MergeAnds (AndConstraint c q) z) => MergeAnds (AndConstraint (NotConstraint (AndConstraint a b)) (OrConstraint x y)) z

instance mergeAndsConstraintNotOrConstraintOrConstraint :: (MergeAnds (OrConstraint x y) q, MergeAnds (AndConstraint (NotConstraint a) (NotConstraint b)) c, MergeAnds (AndConstraint c q) z) => MergeAnds (AndConstraint (NotConstraint (OrConstraint a b)) (OrConstraint x y)) z

-------- and
instance mergeAndsAndConstraintLessThanConstraint :: (MergeAnds (AndConstraint a b) c, MergeAnds (AndConstraint c (LessThanConstraint x)) z) => MergeAnds (AndConstraint (AndConstraint a b) (LessThanConstraint x)) z

instance mergeAndsAndConstraintLessThanOrEqualToConstraint :: (MergeAnds (AndConstraint a b) c, MergeAnds (AndConstraint c (LessThanOrEqualToConstraint x)) z) => MergeAnds (AndConstraint (AndConstraint a b) (LessThanOrEqualToConstraint x)) z

instance mergeAndsAndConstraintNotConstraint :: (MergeAnds (AndConstraint a b) c, MergeAnds (NotConstraint x) y, MergeAnds (AndConstraint c y) z) => MergeAnds (AndConstraint (AndConstraint a b) (NotConstraint x)) z

instance mergeAndsAndConstraintAndConstraint :: (MergeAnds (AndConstraint a b) c, MergeAnds (AndConstraint x y) q, MergeAnds (AndConstraint c q) z) => MergeAnds (AndConstraint (AndConstraint a b) (AndConstraint x y)) z

instance mergeAndsAndConstraintOrConstraint :: (MergeAnds (AndConstraint a b) c, MergeAnds (OrConstraint x y) q, MergeAnds (AndConstraint c q) z) => MergeAnds (AndConstraint (AndConstraint a b) (OrConstraint x y)) z

-----
instance mergeAndsOrConstraintLessThanConstraint :: (MergeAnds (OrConstraint a b) c, MergeAnds (AndConstraint c (LessThanConstraint x)) z) => MergeAnds (AndConstraint (OrConstraint a b) (LessThanConstraint x)) z

instance mergeAndsOrConstraintLessThanOrEqualToConstraint :: (MergeAnds (OrConstraint a b) c, MergeAnds (AndConstraint c (LessThanOrEqualToConstraint x)) z) => MergeAnds (AndConstraint (OrConstraint a b) (LessThanOrEqualToConstraint x)) z

instance mergeAndsOrConstraintNotConstraint :: (MergeAnds (OrConstraint a b) c, MergeAnds (NotConstraint x) y, MergeAnds (AndConstraint c y) z) => MergeAnds (AndConstraint (OrConstraint a b) (NotConstraint x)) z

instance mergeAndsOrConstraintAndConstraint :: (MergeAnds (OrConstraint a b) c, MergeAnds (AndConstraint x y) q, MergeAnds (AndConstraint c q) z) => MergeAnds (AndConstraint (OrConstraint a b) (AndConstraint x y)) z

instance mergeAndsOrConstraintOrConstraint :: (MergeAnds (OrConstraint a b) c, MergeAnds (OrConstraint x y) q, MergeAnds (AndConstraint c q) z) => MergeAnds (AndConstraint (OrConstraint a b) (OrConstraint x y)) z

instance mergeAndsOr :: (MergeAnds a x, MergeAnds b y) => MergeAnds (OrConstraint a b) (OrConstraint x y)

class Add (a :: Rational) (b :: Rational) (c :: Rational) | a b -> c

instance addZP :: Add Zero (PRational a b) (PRational a b)

instance addPZ :: Add (PRational a b) Zero (PRational a b)

instance addZN :: Add Zero (NRational a b) (NRational a b)

instance addNZ :: Add (NRational a b) Zero (NRational a b)

instance addNP :: (ToP n0 _n0, PMul _n0 d1 left, PMul n1 d0 right, PMul d0 d1 d2, ToN left _left, MAdd _left right r, Mul r (PRational POne d2) z) => Add (NRational n0 d0) (PRational n1 d1) z

instance addPN :: (ToP n0 _n0, PMul _n0 d1 left, PMul n1 d0 right, PMul d0 d1 d2, ToN left _left, MAdd _left right r, Mul r (PRational POne d2) z) => Add (PRational n1 d1) (NRational n0 d0) z

instance addZZ :: Add Zero Zero Zero

instance addNN :: (ToP n0 _n0, ToP n1 _n1, PMul _n0 d1 left, PMul _n1 d0 right, PMul d0 d1 d2, PAdd left right _n2, ToN _n2 n2) => Add (NRational n0 d0) (NRational n1 d1) (NRational n2 d2)

instance addPP :: (PMul n0 d1 left, PMul n1 d0 right, PMul d0 d1 d2, PAdd left right n2) => Add (PRational n0 d0) (PRational n1 d1) (PRational n2 d2)

----- subtract two rationals
class Sub (a :: Rational) (b :: Rational) (c :: Rational) | a b -> c

instance sub :: (Add a b c, Flip b d) => Sub a d c

----- invert a rational
class Inv (a :: Rational) (b :: Rational) | a -> b

instance invP :: Inv (PRational a b) (PRational b a)

instance invN :: (ToP a x, ToN b y) => Inv (NRational a b) (NRational y x)

----- divide two rationals
class Div (a :: Rational) (b :: Rational) (c :: Rational) | a b -> c

instance div :: (Mul a b c, Inv c d) => Div a b d

---- adds two rationals
---- uses rank-n types so that qualification can be partially applied
addRationals ::
  forall a.
  Rational a =>
  RatioI a ->
  ( forall b.
    Rational b =>
    RatioI b ->
    ( forall c.
      Rational c =>
      Add a b c =>
      RatioI c
    )
  )
addRationals (R a b) (R x y) = let res = (a % b) + (x % y) in R (DR.numerator res) (DR.denominator res)

infix 6 addRationals as +~

---- subtracts two rationals
---- uses rank-n types so that qualification can be partially applied
subRationals ::
  forall a.
  Rational a =>
  RatioI a ->
  ( forall b.
    Rational b =>
    RatioI b ->
    ( forall c.
      Rational c =>
      Sub a b c =>
      RatioI c
    )
  )
subRationals (R a b) (R x y) = let res = (a % b) - (x % y) in R (DR.numerator res) (DR.denominator res)

infix 6 subRationals as -~

---- multiplies two rationals
---- uses rank-n types so that qualification can be partially applied
mulRationals ::
  forall a.
  Rational a =>
  RatioI a ->
  ( forall b.
    Rational b =>
    RatioI b ->
    ( forall c.
      Rational c =>
      Mul a b c =>
      RatioI c
    )
  )
mulRationals (R a b) (R x y) = let res = (a % b) * (x % y) in R (DR.numerator res) (DR.denominator res)

infix 6 mulRationals as *~

---- divides two rationals
---- uses rank-n types so that qualification can be partially applied
divRationals ::
  forall a.
  Rational a =>
  RatioI a ->
  ( forall b.
    Rational b =>
    RatioI b ->
    ( forall c.
      Rational c =>
      Div a b c =>
      RatioI c
    )
  )
divRationals (R a b) (R x y) = let res = (a % b) / (x % y) in R (DR.numerator res) (DR.denominator res)

infix 6 divRationals as /~

-- allows arbitrary constraints to be added to rationals
inflectLessThan ::
  forall a.
  Rational a =>
  RProxy a ->
  ( forall b c.
    Rational b =>
    ( RatioI b ->
      c
    ) ->
    (LessThan b a True => RatioI b -> c)
  )
inflectLessThan _ a b = a b

inflectLessThanOrEqualTo ::
  forall a.
  Rational a =>
  RProxy a ->
  ( forall b c.
    Rational b =>
    ( RatioI b ->
      c
    ) ->
    (LessThanOrEqualTo b a True => RatioI b -> c)
  )
inflectLessThanOrEqualTo _ a b = a b

inflectGreaterThan ::
  forall a.
  Rational a =>
  RProxy a ->
  ( forall b c.
    Rational b =>
    ( RatioI b ->
      c
    ) ->
    (GreaterThan b a True => RatioI b -> c)
  )
inflectGreaterThan _ a b = a b

inflectGreaterThanOrEqualTo ::
  forall a.
  Rational a =>
  RProxy a ->
  ( forall b c.
    Rational b =>
    ( RatioI b ->
      c
    ) ->
    (GreaterThanOrEqualTo b a True => RatioI b -> c)
  )
inflectGreaterThanOrEqualTo _ a b = a b

----- representation of a rational with numbers
data Ratio (r :: Rational) a b
  = R a b

----- representation of a rational with integers
type RatioI r
  = Ratio r Int Int

----- automatic representation of a rational as an integer
class Rational (a :: Rational) where
  toRational :: RatioI a

instance rationalZ :: Rational Zero where
  toRational = R 0 1

instance rationalPOne :: Rational (PRational POne POne) where
  toRational = R 1 1

instance rationalPS1 :: Rational (PRational n POne) => Rational (PRational (PSuc n) POne) where
  toRational = let (R x y) = (toRational :: RatioI (PRational n POne)) in R (1 + x) y

instance rationalP1S :: Rational (PRational POne n) => Rational (PRational POne (PSuc n)) where
  toRational = let (R x y) = (toRational :: RatioI (PRational POne n)) in R x (1 + y)

instance rationalPSS :: Rational (PRational n m) => Rational (PRational (PSuc n) (PSuc m)) where
  toRational = let (R x y) = (toRational :: RatioI (PRational n m)) in R (x + 1) (y + 1)

instance rationalNOne :: Rational (NRational NOne POne) where
  toRational = R (negate 1) 1

instance rationalNS1 :: Rational (NRational n POne) => Rational (NRational (NSuc n) POne) where
  toRational = let (R x y) = (toRational :: RatioI (NRational n POne)) in R (x - 1) y

instance rationalN1S :: Rational (NRational NOne n) => Rational (NRational NOne (PSuc n)) where
  toRational = let (R x y) = (toRational :: RatioI (NRational NOne n)) in R x (1 + y)

instance rationalNSS :: Rational (NRational n m) => Rational (NRational (NSuc n) (PSuc m)) where
  toRational = let (R x y) = (toRational :: RatioI (NRational n m)) in R (x - 1) (y + 1)

----- rational to a ratio
toRatio :: forall a. Ratio a Int Int -> DR.Ratio Int
toRatio (R a b) = a % b

----- allows for conversion between equal rationals
eqv ::
  forall a b.
  Rational a =>
  Rational b =>
  Equal a b True =>
  RProxy b ->
  RatioI a ->
  RatioI b
eqv _ (R x y) = (R x y)
