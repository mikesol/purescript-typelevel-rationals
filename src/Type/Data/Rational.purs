module Type.Data.Rational where

import Prelude
import Data.Ratio ((%))
import Data.Ratio as DR
import Prim.Boolean (kind Boolean, True, False)
import Type.Data.Boolean (class And, class Not)

----- kinds
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

----- add two rationals
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

---------------
---------------
---------------
---------------
---------------
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
