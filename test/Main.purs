module Test.Main where

import Prelude
import Data.Maybe (Maybe)
import Effect (Effect)
import Effect.Class.Console (log)
import Prim.Boolean (False, True)
import Type.Data.Boolean (BProxy(..))
import Type.Data.Rational (class Add, class AddConstraint, class Equal, class GCD, class GreaterThan, class InvokableRational, class LessThan, class Mod, class Numerator, class PeanoToRational, class Sub, type (&&/), type (+/), type (-/), CRProxy(..), ConstrainedRatio(..), ConstrainedRatioI, EqConstraint, Lt, Lte, N1, N2, N3, N4, Nt, P1, P10, P2, P3, P4, P5, P6, P7, P8, P9, Pe10, Pe2, Pe3, Pe5, Pe6, Pe7, Pe8, PeanoProxy(..), RProxy(..), RatioI, Zero, Pe1, addConstrainedRationals, asConstraintedRational, constConstrained, invoke, invokeTest, resolve, toRational, kind ConstrainedRational)

type Foo
  = (P1 +/ P2)

test0 :: BProxy True
test0 = BProxy :: ∀ b. LessThan (P1 +/ P1) (P2 +/ P1) b => BProxy b

test1 :: BProxy True
test1 = BProxy :: ∀ b. LessThan (P1 +/ P2) (P2 +/ P3) b => BProxy b

test2 :: BProxy False
test2 = BProxy :: ∀ b. LessThan (P2 +/ P3) (P1 +/ P4) b => BProxy b

test3 :: BProxy False
test3 = BProxy :: ∀ b. LessThan (P2 +/ P3) (P2 +/ P3) b => BProxy b

test4 :: BProxy True
test4 = BProxy :: ∀ v b. Add (P1 +/ P2) (P2 +/ P5) v => Equal v (P9 +/ P10) b => BProxy b

test4_1 :: BProxy True
test4_1 = BProxy :: ∀ v b. Sub (P3 +/ P2) (P1 +/ P2) v => Equal v (P1 +/ P1) b => BProxy b

test5 :: BProxy False
test5 = BProxy :: ∀ v b. Add (P1 +/ P3) (P2 +/ P5) v => Equal v (P9 +/ P10) b => BProxy b

test6 :: RProxy (P1 +/ P1)
test6 = RProxy :: forall a. LessThan a (P3 +/ P2) True => GreaterThan a Zero True => RProxy a

test7 :: RProxy (P1 +/ P1)
test7 = RProxy :: ∀ v. Mod (P1 +/ P1) (P6 +/ P1) v => RProxy v

test8 :: RProxy (P1 +/ P1)
test8 = RProxy :: ∀ v. Mod (P7 +/ P1) (P6 +/ P1) v => RProxy v

test9_1 :: PeanoProxy Pe2
test9_1 = PeanoProxy :: forall c. Numerator (P2 +/ P7) c => PeanoProxy c

test9_2 :: RProxy (P3 +/ P1)
test9_2 = RProxy :: forall c. PeanoToRational Pe3 c => RProxy c

test9 :: PeanoProxy Pe2
test9 = PeanoProxy :: forall c. GCD Pe8 Pe6 c => PeanoProxy c

test9_3 :: PeanoProxy Pe5
test9_3 = PeanoProxy :: forall c. GCD Pe10 Pe5 c => PeanoProxy c

test9_4 :: PeanoProxy Pe1
test9_4 = PeanoProxy :: forall c. GCD Pe7 Pe5 c => PeanoProxy c

testf0 :: CRProxy (Lt (P3 +/ P2)) -> CRProxy (Lt Zero)
testf0 _ = CRProxy

testf0_1 :: CRProxy (Lt Zero)
testf0_1 = invokeTest (BProxy :: BProxy True) testf0 (CRProxy :: CRProxy (Lt (P1 +/ P2)))

testf0_2 :: CRProxy (Lt Zero)
testf0_2 = invokeTest (BProxy :: BProxy True) testf0 (CRProxy :: CRProxy ((Lt Zero) &&/ (Lt (N2 -/ P5))))

testf0_3 :: CRProxy (Lt Zero)
testf0_3 = invokeTest (BProxy :: BProxy True) testf0 (CRProxy :: CRProxy ((Lt Zero) &&/ (Nt (Lt (N2 -/ P5)))))

testf0_4 :: CRProxy (Lt Zero)
testf0_4 = invokeTest (BProxy :: BProxy True) testf0 (CRProxy :: CRProxy ((Nt (Lt (N2 -/ P5))) &&/ (Lt Zero)))

testf0__1 :: CRProxy (Lt Zero)
testf0__1 = invokeTest (BProxy :: BProxy False) testf0 (CRProxy :: CRProxy (Lt (P5 +/ P2)))

testf0__2 :: CRProxy (Lt Zero)
testf0__2 = invokeTest (BProxy :: BProxy False) testf0 (CRProxy :: CRProxy ((Nt (Lt (N2 -/ P5))) &&/ (Lt (P2 +/ P1))))

resolveTest0 :: RatioI Zero
resolveTest0 = resolve (CRProxy :: CRProxy ((Nt (Lt Zero)) &&/ (Lte Zero)))

resolveTest1 :: RatioI (P1 +/ P5)
resolveTest1 = resolve (CRProxy :: CRProxy ((Nt (Lt (P1 +/ P5))) &&/ (Lte (P1 +/ P5))))

-- these all correctly fail
-- resolveTest1 :: forall t4391. ResolvableRationalInternal ( (Nt (Lt (P1 +/ P1))) &&/ (Lte Zero)) t4391 => Rational t4391 => RatioI t4391
-- resolveTest1 = resolve (CRProxy :: CRProxy ( (Nt (Lt (P1 +/ P1))) &&/ (Lte Zero)))
-- resolveTest2 = resolve (CRProxy :: CRProxy ( (Nt (Lt (P1 +/ P1))) &&/ (Lte Zero)))
addLessThanZero =
  addConstrainedRationals ::
    InvokableRational (Lt Zero) (Lt Zero) =>
    ConstrainedRatioI (Lt Zero) ->
    ( InvokableRational (Lt Zero) (Lt Zero) =>
      ConstrainedRatioI (Lt Zero) ->
      ( forall (c :: ConstrainedRational).
        AddConstraint (Lt Zero) (Lt Zero) c =>
        ConstrainedRatioI c
      )
    )

lt0 = ((CR (negate 51) 3) :: InvokableRational (Lt Zero) (Lt Zero) => ConstrainedRatioI (Lt Zero))

testAdd :: forall (c :: ConstrainedRational). AddConstraint (Lt Zero) (Lt Zero) c => ConstrainedRatioI c
testAdd = addLessThanZero lt0 lt0

-- this correctly fails
-- testAddSpecializedFail = testAdd :: ConstrainedRatioI (Lt (P1 +/ P1))
testAddSpecialized = testAdd :: ConstrainedRatioI (Lt Zero)

testfneg :: ConstrainedRatioI (Lt (N3 -/ P2)) -> ConstrainedRatioI (Lt (N4 -/ P2))
testfneg _ = (CR (negate 100) 2)

testfpos :: ConstrainedRatioI (Lt (P3 +/ P2)) -> ConstrainedRatioI (Lt (P3 +/ P2))
testfpos _ = (CR 5 2)

-- fails as expected
-- testInvoke = invoke testfneg testAdd
testInvoke :: ConstrainedRatio (Lt (P3 +/ P2)) Int Int
testInvoke = invoke testfpos testAdd

----- for the blog article
oneHalfPrecise =
  asConstraintedRational 1 2 ::
    Maybe
      ( ConstrainedRatioI
          ( ( Nt
                (Lt (P1 +/ P2))
            )
              &&/ (Lt (P1 +/ P2))
          )
      )

returnAQuarter ::
  ConstrainedRatioI
    ( ( Nt
          (Lt Zero)
      )
        &&/ (Lt (P1 +/ P1))
    ) ->
  ConstrainedRatioI
    ( ( Nt
          (Lt (P1 +/ P4))
      )
        &&/ (Lte (P1 +/ P4))
    )
returnAQuarter _ =
  constConstrained
    ( resolve
        ( CRProxy ::
            CRProxy
              ( ( Nt
                    (Lt (P1 +/ P4))
                )
                  &&/ (Lte (P1 +/ P4))
              )
        )
    )

myQuarterBack :: Maybe (ConstrainedRatioI ((Nt (Lt (P1 +/ P4))) &&/ (Lte (P1 +/ P4))))
myQuarterBack = invoke returnAQuarter <$> oneHalfPrecise

threeHalvesPrecise =
  asConstraintedRational 3 2 ::
    Maybe
      ( ConstrainedRatioI
          ( ( Nt
                (Lt (P3 +/ P2))
            )
              &&/ (Lt (P3 +/ P2))
          )
      )

-- myQuarterBackRed = invoke returnAQuarter <$> threeHalvesPrecise
main :: Effect Unit
main = do
  log (show ((toRational :: RatioI (N1 -/ P3))))
  log (show ((asConstraintedRational 3 2 :: Maybe (ConstrainedRatioI (Lte (P3 +/ P2))))))
  log (show ((asConstraintedRational 1 2 :: Maybe (ConstrainedRatioI (Lte (P3 +/ P2))))))
  log (show ((asConstraintedRational 5 2 :: Maybe (ConstrainedRatioI (Lte (P3 +/ P2))))))
  let
    oneHalf =
      asConstraintedRational 1 2 ::
        Maybe
          ( ConstrainedRatioI
              ( ( Nt
                    (Lt Zero)
                )
                  &&/ (Lt (P1 +/ P1))
              )
          )
  void $ pure unit

----------------------- further testing add function for those interested
addLessThanZero' =
  addConstrainedRationals ::
    forall (a :: ConstrainedRational).
    InvokableRational (Lt Zero) a =>
    ConstrainedRatioI (Lt Zero) ->
    ( forall (b :: ConstrainedRational).
      InvokableRational (Lt Zero) b =>
      ConstrainedRatioI (Lt Zero) ->
      ( forall (c :: ConstrainedRational).
        AddConstraint a b c =>
        ConstrainedRatioI c
      )
    )

step0 ::
  ConstrainedRatioI (Lt Zero) ->
  ( forall (c :: ConstrainedRational).
    AddConstraint (Lt Zero) (Lt Zero) c =>
    ConstrainedRatioI c
  )
step0 = invoke addLessThanZero' lt0'

lt0' = ((CR (negate 51) 3) :: ConstrainedRatioI (Lt Zero))

testAdd' :: forall (c :: ConstrainedRational). AddConstraint (Lt Zero) (Lt Zero) c => ConstrainedRatioI c
testAdd' = invoke step0 lt0'

-- this correctly fails
-- testAddSpecializedFail = testAdd :: ConstrainedRatioI (Lt (P1 +/ P1))
testAddSpecialized' = testAdd' :: ConstrainedRatioI (Lt Zero)

testfneg' :: ConstrainedRatioI (Lt (N3 -/ P2)) -> ConstrainedRatioI (Lt (N4 -/ P2))
testfneg' _ = (CR (negate 100) 2)

testfpos' :: ConstrainedRatioI (Lt (P3 +/ P2)) -> ConstrainedRatioI (Lt (P3 +/ P2))
testfpos' _ = (CR 5 2)

-- fails as expected
--testInvoke'' = invoke testfneg' testAdd'
testInvoke' :: ConstrainedRatio (Lt (P3 +/ P2)) Int Int
testInvoke' = invoke testfpos' testAdd'

type Gte0lt1
  = ((Nt (Lt Zero)) &&/ (Lt (P1 +/ P1)))

type IsOneHalf
  = EqConstraint (P1 +/ P2)

type IsOne
  = ((Nt (Lt (P4 +/ P4))) &&/ (Lt (P4 +/ P4)))

type Between0And1
  = ConstrainedRatioI
      ( ( Nt
            (Lt Zero)
        )
          &&/ (Lt (P1 +/ P1))
      )

firstStep =
  addConstrainedRationals ::
    forall (a :: ConstrainedRational).
    InvokableRational
      Gte0lt1
      a =>
    Between0And1 ->
    ( forall (b :: ConstrainedRational).
      InvokableRational
        Gte0lt1
        b =>
      Between0And1 ->
      ( forall (c :: ConstrainedRational).
        AddConstraint a b c =>
        ConstrainedRatioI c
      )
    )

addTwoHalves ::
  ConstrainedRatioI IsOneHalf ->
  ConstrainedRatioI IsOneHalf ->
  ConstrainedRatioI IsOne
addTwoHalves i0 i1 = finalStep
  where
  curryFirstArg ::
    Between0And1 ->
    ( forall (c :: ConstrainedRational).
      AddConstraint
        IsOneHalf
        IsOneHalf
        c =>
      (ConstrainedRatioI c)
    )
  curryFirstArg = invoke firstStep i0

  finalStep ::
    forall (c :: ConstrainedRational).
    AddConstraint
      IsOneHalf
      IsOneHalf
      c =>
    ConstrainedRatioI c
  finalStep = invoke curryFirstArg i1
