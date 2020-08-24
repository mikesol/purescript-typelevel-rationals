module Test.Main where

import Prelude
import Effect (Effect)
import Prim.Boolean (False, True)
import Type.Data.Boolean (BProxy(..))
import Type.Data.Rational (class Add, class GreaterThan, class LessThan, P1, P10, P2, P3, P4, PRational, Zero, class Equal, P5, P9, RProxy(..))

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

main :: Effect Unit
main = pure unit
