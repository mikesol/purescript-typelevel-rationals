module Test.Main where

import Prelude
import Data.Maybe (Maybe)
import Effect (Effect)
import Effect.Class.Console (log)
import Prim.Boolean (False, True)
import Type.Data.Boolean (BProxy(..))
import Type.Data.Rational (class Add, class AddConstraint, class Equal, class GreaterThan, class InvokableRational, class LessThan, AndConstraint, CRProxy(..), ConstrainedRatio(..), ConstrainedRatioI, LessThanConstraint, LessThanOrEqualToConstraint, N2, N3, N4, NRational, NotConstraint, P1, P10, P2, P3, P4, P5, P9, PRational, RProxy(..), RatioI, Zero, addConstrainedRationals, asConstraintedRational, constConstrained, invoke, invokeTest, resolve, kind ConstrainedRational)

test0 :: BProxy True
test0 = BProxy :: ∀ b. LessThan (PRational P1 P1) (PRational P2 P1) b => BProxy b

test1 :: BProxy True
test1 = BProxy :: ∀ b. LessThan (PRational P1 P2) (PRational P2 P3) b => BProxy b

test2 :: BProxy False
test2 = BProxy :: ∀ b. LessThan (PRational P2 P3) (PRational P1 P4) b => BProxy b

test3 :: BProxy False
test3 = BProxy :: ∀ b. LessThan (PRational P2 P3) (PRational P2 P3) b => BProxy b

test4 :: BProxy True
test4 = BProxy :: ∀ v b. Add (PRational P1 P2) (PRational P2 P5) v => Equal v (PRational P9 P10) b => BProxy b

test5 :: BProxy False
test5 = BProxy :: ∀ v b. Add (PRational P1 P3) (PRational P2 P5) v => Equal v (PRational P9 P10) b => BProxy b

test6 :: RProxy (PRational P1 P1)
test6 = RProxy :: forall a. LessThan a (PRational P3 P2) True => GreaterThan a Zero True => RProxy a

testf0 :: CRProxy (LessThanConstraint (PRational P3 P2)) -> CRProxy (LessThanConstraint Zero)
testf0 _ = CRProxy

testf0_1 :: CRProxy (LessThanConstraint Zero)
testf0_1 = invokeTest (BProxy :: BProxy True) testf0 (CRProxy :: CRProxy (LessThanConstraint (PRational P1 P2)))

testf0_2 :: CRProxy (LessThanConstraint Zero)
testf0_2 = invokeTest (BProxy :: BProxy True) testf0 (CRProxy :: CRProxy (AndConstraint (LessThanConstraint Zero) (LessThanConstraint (NRational N2 P5))))

testf0_3 :: CRProxy (LessThanConstraint Zero)
testf0_3 = invokeTest (BProxy :: BProxy True) testf0 (CRProxy :: CRProxy (AndConstraint (LessThanConstraint Zero) (NotConstraint (LessThanConstraint (NRational N2 P5)))))

testf0_4 :: CRProxy (LessThanConstraint Zero)
testf0_4 = invokeTest (BProxy :: BProxy True) testf0 (CRProxy :: CRProxy (AndConstraint (NotConstraint (LessThanConstraint (NRational N2 P5))) (LessThanConstraint Zero)))

testf0__1 :: CRProxy (LessThanConstraint Zero)
testf0__1 = invokeTest (BProxy :: BProxy False) testf0 (CRProxy :: CRProxy (LessThanConstraint (PRational P5 P2)))

testf0__2 :: CRProxy (LessThanConstraint Zero)
testf0__2 = invokeTest (BProxy :: BProxy False) testf0 (CRProxy :: CRProxy (AndConstraint (NotConstraint (LessThanConstraint (NRational N2 P5))) (LessThanConstraint (PRational P2 P1))))

resolveTest0 :: RatioI Zero
resolveTest0 = resolve (CRProxy :: CRProxy (AndConstraint (NotConstraint (LessThanConstraint Zero)) (LessThanOrEqualToConstraint Zero)))

resolveTest1 :: RatioI (PRational P1 P5)
resolveTest1 = resolve (CRProxy :: CRProxy (AndConstraint (NotConstraint (LessThanConstraint (PRational P1 P5))) (LessThanOrEqualToConstraint (PRational P1 P5))))

-- these all correctly fail
-- resolveTest1 :: forall t4391. ResolvableRationalInternal (AndConstraint (NotConstraint (LessThanConstraint (PRational P1 P1))) (LessThanOrEqualToConstraint Zero)) t4391 => Rational t4391 => RatioI t4391
-- resolveTest1 = resolve (CRProxy :: CRProxy (AndConstraint (NotConstraint (LessThanConstraint (PRational P1 P1))) (LessThanOrEqualToConstraint Zero)))
-- resolveTest2 = resolve (CRProxy :: CRProxy (AndConstraint (NotConstraint (LessThanConstraint (PRational P1 P1))) (LessThanOrEqualToConstraint Zero)))
addLessThanZero =
  addConstrainedRationals ::
    InvokableRational (LessThanConstraint Zero) (LessThanConstraint Zero) =>
    ConstrainedRatioI (LessThanConstraint Zero) ->
    ( InvokableRational (LessThanConstraint Zero) (LessThanConstraint Zero) =>
      ConstrainedRatioI (LessThanConstraint Zero) ->
      ( forall (c :: ConstrainedRational).
        AddConstraint (LessThanConstraint Zero) (LessThanConstraint Zero) c =>
        ConstrainedRatioI c
      )
    )

lt0 = ((CR (negate 51) 3) :: InvokableRational (LessThanConstraint Zero) (LessThanConstraint Zero) => ConstrainedRatioI (LessThanConstraint Zero))

testAdd :: forall (c :: ConstrainedRational). AddConstraint (LessThanConstraint Zero) (LessThanConstraint Zero) c => ConstrainedRatioI c
testAdd = addLessThanZero lt0 lt0

-- this correctly fails
-- testAddSpecializedFail = testAdd :: ConstrainedRatioI (LessThanConstraint (PRational P1 P1))
testAddSpecialized = testAdd :: ConstrainedRatioI (LessThanConstraint Zero)

testfneg :: ConstrainedRatioI (LessThanConstraint (NRational N3 P2)) -> ConstrainedRatioI (LessThanConstraint (NRational N4 P2))
testfneg _ = (CR (negate 100) 2)

testfpos :: ConstrainedRatioI (LessThanConstraint (PRational P3 P2)) -> ConstrainedRatioI (LessThanConstraint (PRational P3 P2))
testfpos _ = (CR 5 2)

-- fails as expected
-- testInvoke = invoke testfneg testAdd
testInvoke :: ConstrainedRatio (LessThanConstraint (PRational P3 P2)) Int Int
testInvoke = invoke testfpos testAdd

----- for the blog article
oneHalfPrecise =
  asConstraintedRational 1 2 ::
    Maybe
      ( ConstrainedRatioI
          ( AndConstraint
              ( NotConstraint
                  (LessThanConstraint (PRational P1 P2))
              )
              (LessThanConstraint (PRational P1 P2))
          )
      )

returnAQuarter ::
  ConstrainedRatioI
    ( AndConstraint
        ( NotConstraint
            (LessThanConstraint Zero)
        )
        (LessThanConstraint (PRational P1 P1))
    ) ->
  ConstrainedRatioI
    ( AndConstraint
        ( NotConstraint
            (LessThanConstraint (PRational P1 P4))
        )
        (LessThanOrEqualToConstraint (PRational P1 P4))
    )
returnAQuarter _ =
  constConstrained
    ( resolve
        ( CRProxy ::
            CRProxy
              ( AndConstraint
                  ( NotConstraint
                      (LessThanConstraint (PRational P1 P4))
                  )
                  (LessThanOrEqualToConstraint (PRational P1 P4))
              )
        )
    )

myQuarterBack ::
  ConstrainedRatioI
    ( AndConstraint
        ( NotConstraint
            (LessThanConstraint (PRational P1 P4))
        )
        (LessThanOrEqualToConstraint (PRational P1 P4))
    )
myQuarterBack =
  invoke returnAQuarter
    ( (CR 1 2) ::
        ConstrainedRatioI
          ( AndConstraint
              ( NotConstraint
                  (LessThanConstraint (PRational P1 P2))
              )
              (LessThanConstraint (PRational P1 P2))
          )
    )

main :: Effect Unit
main = do
  log (show ((asConstraintedRational 3 2 :: Maybe (ConstrainedRatioI (LessThanOrEqualToConstraint (PRational P3 P2))))))
  log (show ((asConstraintedRational 1 2 :: Maybe (ConstrainedRatioI (LessThanOrEqualToConstraint (PRational P3 P2))))))
  log (show ((asConstraintedRational 5 2 :: Maybe (ConstrainedRatioI (LessThanOrEqualToConstraint (PRational P3 P2))))))
  let
    oneHalf =
      asConstraintedRational 1 2 ::
        Maybe
          ( ConstrainedRatioI
              ( AndConstraint
                  ( NotConstraint
                      (LessThanConstraint Zero)
                  )
                  (LessThanConstraint (PRational P1 P1))
              )
          )
  void $ pure unit
