{-
Welcome to a Spago project!
You can edit this file as you like.
-}
{ name = "purescript-typelevl-rationals"
, dependencies =
  [ "arrays"
  , "console"
  , "effect"
  , "psci-support"
  , "rationals"
  , "typelevel-prelude"
  , "unsafe-coerce"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs", "test/**/*.purs" ]
}
