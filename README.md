# purescript-typelevel-rationals

Typelevel rationals in PureScript.

```purescript
-- to be read as
-- 1/1 is less than 3/2 and greater than zero
test :: RProxy (PRational P1 P1)
test = RProxy :: forall a. LessThan a (PRational P3 P2) True => GreaterThan a Zero True => RProxy a
```
